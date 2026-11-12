(* Bytestring phases on arbitrary runtime variable maps. *)
Theory abiEncoderWindowBytes
Ancestors
  abiEncoderWindowSequence abiEncoderBytesCode abiEncoderRounding
  abiEncoderWindow abiEncoderMemory abiEncoderPrimitiveEffect
  abiEncoderRegisteredEffect abiEncoderWindowContract contractABI valueEncoding valueEncodingProps
  abiEncoderWindowLeaves abiEncoderBytes abiEncoderWrites emitHelperProps
  exprLoweringProps localPtrsProps abiEncoderExtendSim venomMemDefs
  emitHelper compileEnv loweringStateRelDefs freshWrites venomState venomExecSemantics venomInst words arithmetic
  abiEncoder list rich_list abiEncoderWindowLookup

Theorem window_bytes_output_bounds:
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) st = (out,st') ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\
             EVERY (not_fresh_at st') i.inst_outputs) (emitted_insts st st')
Proof
  simp[Once compile_abi_encode_child_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, not_fresh_at_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem window_round_sequence:
  abi_encode_round len st = (out,st') /\
  eval_operand len s = SOME (n2w cnt) /\ cnt + 31 < dimword (:256) ==>
  ?t. window_pure_seq st st' s t /\
    eval_operand out t = SOME (n2w (contractABI$ceil32 cnt)) /\
    (!x. out = Var x ==> not_fresh_at st' x)
Proof
  simp_tac bool_ss [abi_encode_round_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [Lit 31w;len] st = (arg,c1)` >>
  rename1 `emit_op AND _ c1 = (out,end_st)` >>
  drule window_emit_add_pure >>
  disch_then (qspec_then `s` mp_tac) >>
  simp[eval_operand_def] >> strip_tac >>
  drule window_emit_and_pure >>
  disch_then (qspec_then `t` mp_tac) >>
  simp[eval_operand_def, abi_encoder_round_ceil32] >> strip_tac >>
  qexists_tac `t'` >> simp[] >>
  metis_tac[window_pure_seq_chain]
QED

Theorem window_emit_not_pure[local]:
  emit_op NOT [arg] st = (out,st') /\ eval_operand arg s = SOME a ==>
  ?t. window_pure_seq st st' s t /\ eval_operand out t = SOME (word_1comp a) /\
    (!x. out = Var x ==> not_fresh_at st' x)
Proof
  strip_tac >>
  `run_inst_seq (emitted_insts st st') s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) (word_1comp a) s)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     drule step_NOT >> simp[run_inst_seq_def]) >>
  qexists_tac `update_var (STRING #"%" (toString st.cs_next_var)) (word_1comp a) s` >>
  irule window_emit_register_pure >> (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`[arg]`, `NOT`] >> simp[is_terminator_def]
QED

(* The NOT writes the next fresh name before the ADD reads len, so len must
   already be allocated. *)
Theorem window_ceil32_sequence:
  abi_encode_ceil32 len st = (out,st') /\
  eval_operand len s = SOME (n2w cnt) /\
  (!x. len = Var x ==> not_fresh_at st x) /\ cnt + 31 < dimword (:256) ==>
  ?t. window_pure_seq st st' s t /\
    eval_operand out t = SOME (n2w (contractABI$ceil32 cnt)) /\
    (!x. out = Var x ==> not_fresh_at st' x)
Proof
  simp_tac bool_ss [abi_encode_ceil32_def, comp_bind_def, LET_THM] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op NOT [Lit 31w] st = (mask,c1)` >>
  rename1 `emit_op ADD [len;Lit 31w] c1 = (arg,c2)` >>
  mp_tac (Q.INST [`arg` |-> `Lit 31w`, `out` |-> `mask`, `st'` |-> `c1`,
    `a` |-> `31w:bytes32`] window_emit_not_pure) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `window_pure_seq st c1 s s1` >>
  `eval_operand len s1 = SOME (n2w cnt)` by
    metis_tac[window_seq_eval, window_pure_seq_def] >>
  mp_tac (Q.INST [`lhs` |-> `len`, `rhs` |-> `Lit 31w`, `out` |-> `arg`, `st` |-> `c1`,
    `st'` |-> `c2`, `s` |-> `s1:venom_state`, `a` |-> `n2w cnt:bytes32`,
    `b` |-> `31w:bytes32`] window_emit_add_pure) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `window_pure_seq c1 c2 s1 s2` >>
  `eval_operand mask s2 = SOME (word_1comp 31w)` by
    metis_tac[window_seq_eval, window_pure_seq_def] >>
  mp_tac (Q.INST [`lhs` |-> `arg`, `rhs` |-> `mask`, `st` |-> `c2`,
    `s` |-> `s2:venom_state`, `a` |-> `n2w cnt + 31w:bytes32`,
    `b` |-> `word_1comp (31w:bytes32)`] window_emit_and_pure) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `window_pure_seq c2 st' s2 actual` >>
  `(n2w cnt + 31w:bytes32) && word_1comp 31w = n2w (contractABI$ceil32 cnt)` by
    (`word_1comp (31w:bytes32) =
      0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w` by
       simp_tac std_ss [word_1comp_n2w, dimword_def, venomMemPropsTheory.dimindex_256] >>
     asm_rewrite_tac [] >> ONCE_REWRITE_TAC [WORD_AND_COMM] >>
     ONCE_REWRITE_TAC [WORD_ADD_COMM] >> irule abi_encoder_round_ceil32 >>
     asm_simp_tac (srw_ss()) []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  qpat_x_assum `window_pure_seq st c1 s s1` (fn a =>
    qpat_x_assum `window_pure_seq c1 c2 s1 s2` (fn b =>
      assume_tac (MATCH_MP window_pure_seq_chain (CONJ a b)))) >>
  qpat_x_assum `window_pure_seq st c2 s s2` (fn a =>
    qpat_x_assum `window_pure_seq c2 st' s2 actual` (fn b =>
      ACCEPT_TAC (MATCH_MP window_pure_seq_chain (CONJ a b))))
QED

Theorem window_bytes_suffix_sequence:
  abi_encode_bytes_suffix len st = (out,st') /\
  eval_operand len s = SOME (n2w cnt) /\
  (!x. len = Var x ==> not_fresh_at st x) /\ cnt + 31 < dimword (:256) ==>
  ?t. window_pure_seq st st' s t /\
    eval_operand out t = SOME (n2w (32 + contractABI$ceil32 cnt)) /\
    (!x. out = Var x ==> not_fresh_at st' x)
Proof
  simp_tac bool_ss [abi_encode_bytes_suffix_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule_all window_ceil32_sequence >> strip_tac >>
  drule window_emit_add_pure >>
  disch_then (qspec_then `t` mp_tac) >>
  simp[eval_operand_def, word_add_n2w] >> strip_tac >>
  qexists_tac `t'` >> simp[] >> metis_tac[window_pure_seq_chain]
QED

Theorem window_bytes_prefix_sequence:
  abi_encode_bytes_prefix dst src st = (ops,st') /\
  eval_operand src s = SOME (n2w sb) /\ mload sb s = n2w cnt /\
  eval_operand dst s = SOME (n2w db) /\
  (!x. dst = Var x ==> not_fresh_at st x) /\
  sb < dimword (:256) /\ cnt + 31 < dimword (:256) ==>
  ?t. window_pure_seq st st' s t /\
    eval_operand (FST ops) t = SOME (n2w cnt) /\
    eval_operand (SND ops) t = SOME (n2w (db + contractABI$ceil32 cnt)) /\
    (!x. FST ops = Var x ==> not_fresh_at st' x) /\
    (!x. SND ops = Var x ==> not_fresh_at st' x)
Proof
  simp_tac bool_ss [abi_encode_bytes_prefix_def, comp_bind_def,
    comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op MLOAD [src] st = (len,c1)` >>
  rename1 `abi_encode_round len c1 = (rounded,c2)` >>
  rename1 `emit_op ADD [dst;rounded] c2 = (lastptr,ready)` >>
  drule_all window_emit_load_pure >> strip_tac >>
  rename1 `window_pure_seq st c1 s loaded` >>
  `eval_operand len loaded = SOME (n2w cnt)` by metis_tac[] >>
  drule_all window_round_sequence >> strip_tac >>
  rename1 `window_pure_seq c1 c2 loaded prepared` >>
  `window_pure_seq st c2 s prepared` by metis_tac[window_pure_seq_chain] >>
  `eval_operand dst prepared = SOME (n2w db)` by
    metis_tac[window_seq_eval, window_pure_seq_def] >>
  drule_all window_emit_add_pure >> strip_tac >>
  rename1 `window_pure_seq c2 ready prepared actual` >>
  `window_pure_seq c1 ready loaded actual` by metis_tac[window_pure_seq_chain] >>
  `eval_operand len actual = SOME (n2w cnt)` by
    metis_tac[window_seq_eval, window_pure_seq_def] >>
  qexists_tac `actual` >> simp[word_add_n2w] >>
  conj_tac >- metis_tac[window_pure_seq_chain] >>
  metis_tac[not_fresh_at_mono, window_seq_mono, window_pure_seq_def]
QED

Theorem window_bytes_store_sequence[local]:
  emit_void MSTORE [ptr_op;value_op] st = ((),st') /\
  eval_operand ptr_op s = SOME (n2w p) /\ eval_operand value_op s = SOME w /\
  p < dimword (:256) ==>
  window_seq st st' s (mstore p w s)
Proof
  strip_tac >> drule_all window_emit_store_run >> strip_tac >>
  simp[window_seq_def, mstore_def, write_memory_with_expansion_def,
    lookup_var_def] >>
  gvs[emit_void_def, fresh_id_def, emit_def, comp_bind_def, comp_return_def]
QED

Theorem window_bytes_mcopy_sequence[local]:
  emit_void MCOPY [dst;src;len] st = ((),st') /\
  eval_operand dst s = SOME (n2w db) /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand len s = SOME (n2w cnt) /\
  db < dimword (:256) /\ sb < dimword (:256) /\ cnt < dimword (:256) ==>
  window_seq st st' s (mcopy db sb cnt s)
Proof
  strip_tac >> drule_all window_emit_copy_run >> strip_tac >>
  simp[window_seq_def, mcopy_def, write_memory_with_expansion_def,
    lookup_var_def] >>
  gvs[emit_void_def, fresh_id_def, emit_def, comp_bind_def, comp_return_def]
QED

Theorem window_bytes_copy_sequence:
  abi_encode_bytes_copy dst src len lastptr st = ((),st') /\
  eval_operand dst s = SOME (n2w db) /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand len s = SOME (n2w cnt) /\
  eval_operand lastptr s = SOME (n2w (db+rounded)) /\
  db+rounded < dimword (:256) /\ sb < dimword (:256) /\ 32+cnt < dimword (:256) /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at st x) ==>
  ?t. window_seq st st' s t /\
    t.vs_memory = (mcopy db sb (32+cnt) (mstore (db+rounded) 0w s)).vs_memory /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests /\
    t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx /\
    t.vs_immutables = s.vs_immutables /\ t.vs_outcomes = s.vs_outcomes /\
    t.vs_pending_deletions = s.vs_pending_deletions
Proof
  simp_tac bool_ss [abi_encode_bytes_copy_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_void MSTORE [lastptr;Lit 0w] st = ((),c1)` >>
  rename1 `emit_op ADD [Lit 32w;len] c1 = (copylen,c2)` >>
  rename1 `emit_void MCOPY [dst;src;copylen] c2 = ((),end_st)` >>
  `window_seq st c1 s (mstore (db+rounded) 0w s)` by
    (irule window_bytes_store_sequence >> (conj_tac >- simp[]) >>
     qexistsl_tac [`lastptr`, `Lit 0w`] >> simp[eval_operand_def]) >>
  `eval_operand len (mstore (db+rounded) 0w s) = SOME (n2w cnt)` by
    simp[eval_operand_mstore] >>
  drule window_emit_add_pure >>
  disch_then (qspec_then `mstore (db+rounded) 0w s` mp_tac) >>
  simp[eval_operand_def, eval_operand_mstore, word_add_n2w] >> strip_tac >>
  rename1 `window_pure_seq c1 c2 _ prepared` >>
  `window_seq st c2 s prepared` by
    metis_tac[window_seq_chain, window_pure_seq_def] >>
  `eval_operand dst prepared = SOME (n2w db) /\
   eval_operand src prepared = SOME (n2w sb)` by
    metis_tac[window_seq_eval] >>
  `db < dimword (:256)` by decide_tac >>
  `window_seq c2 end_st prepared (mcopy db sb (32+cnt) prepared)` by
    (irule window_bytes_mcopy_sequence >>
     simp[] >> qexistsl_tac [`dst`, `copylen`, `src`] >> simp[]) >>
  qexists_tac `mcopy db sb (32+cnt) prepared` >>
  conj_tac >- metis_tac[window_seq_chain] >>
  fs[window_pure_seq_def] >>
  conj_tac >- (irule abi_encoder_copy_memory >> simp[]) >>
  simp_tac (srw_ss()) [mcopy_def, write_memory_with_expansion_def, LET_THM] >>
  qpat_x_assum `prepared.vs_current_bb = _` mp_tac >>
  qpat_x_assum `prepared.vs_inst_idx = _` mp_tac >>
  qpat_x_assum `prepared.vs_accounts = _` mp_tac >>
  qpat_x_assum `prepared.vs_transient = _` mp_tac >>
  qpat_x_assum `prepared.vs_logs = _` mp_tac >>
  qpat_x_assum `prepared.vs_pending_deletions = _` mp_tac >>
  qpat_x_assum `prepared.vs_tx_ctx = _` mp_tac >>
  qpat_x_assum `prepared.vs_block_ctx = _` mp_tac >>
  qpat_x_assum `prepared.vs_immutables = _` mp_tac >>
  qpat_x_assum `prepared.vs_outcomes = _` mp_tac >>
  simp_tac (srw_ss()) [mstore_def, write_memory_with_expansion_def, LET_THM] >>
  simp[]
QED

Theorem window_bytes_input_memory:
  abi_encoder_window_input (AbiBytestring maxlen) at (BytesV bs) sb cap s.vs_memory /\
  (sb + cap <= db \/ db + LENGTH (enc at (BytesV bs)) <= sb) ==>
  mem_bytes_at db (LENGTH (enc at (BytesV bs)))
    (mcopy db sb (32+LENGTH bs)
      (mstore (db+contractABI$ceil32 (LENGTH bs)) 0w s)).vs_memory =
    enc at (BytesV bs)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  mp_tac (Q.INST [`at` |-> `at`, `bs` |-> `bs:word8 list`] abi_encoder_bytes_encoding) >>
  (impl_tac >- metis_tac[abi_encoder_window_bytes_iff]) >> strip_tac >>
  `32 + LENGTH bs <= cap /\
   mem_word_at sb s.vs_memory = n2w (LENGTH bs) /\
   mem_bytes_at (sb+32) (LENGTH bs) s.vs_memory = bs` by
    (fs[abi_encoder_window_bytes_iff]) >>
  `LENGTH bs <= contractABI$ceil32 (LENGTH bs) /\
   contractABI$ceil32 (LENGTH bs) <= LENGTH bs + 32` by
    (mp_tac (Q.INST [`cnt` |-> `LENGTH (bs:word8 list)`] abi_encoder_ceil32_bounds) >>
     decide_tac) >>
  mp_tac (Q.INST [`bs` |-> `bs:word8 list`,
    `rounded` |-> `contractABI$ceil32 (LENGTH bs)`] abi_encoder_bytes_zero_copy) >>
  (impl_tac >- (asm_rewrite_tac[] >> decide_tac)) >>
  asm_rewrite_tac[]
QED

Theorem window_bytes_body_sequence:
  abi_encode_bytes_prefix dst src st = (ops,ready) /\
  abi_encode_bytes_copy dst src (FST ops) (SND ops) ready = ((),copied) /\
  eval_operand src s = SOME (n2w sb) /\ mload sb s = n2w cnt /\
  eval_operand dst s = SOME (n2w db) /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at st x) /\
  sb < dimword (:256) /\ cnt+31 < dimword (:256) /\
  db+contractABI$ceil32 cnt < dimword (:256) /\ 32+cnt < dimword (:256) ==>
  ?t. window_seq st copied s t /\
    eval_operand (FST ops) t = SOME (n2w cnt) /\
    (!x. FST ops = Var x ==> not_fresh_at copied x) /\
    t.vs_memory = (mcopy db sb (32+cnt) (mstore (db+contractABI$ceil32 cnt) 0w s)).vs_memory /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests /\
    t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx /\
    t.vs_immutables = s.vs_immutables /\ t.vs_outcomes = s.vs_outcomes /\
    t.vs_pending_deletions = s.vs_pending_deletions
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
  rename1 `window_seq ready copied prepared actual` >>
  `eval_operand (FST ops) actual = SOME (n2w cnt)` by
    metis_tac[window_seq_eval] >>
  qexists_tac `actual` >> simp[] >>
  conj_tac >- metis_tac[window_seq_chain, window_pure_seq_def] >>
  conj_tac >- metis_tac[not_fresh_at_mono, window_seq_mono] >>
  conj_tac >-
    (irule EQ_TRANS >>
     qexists_tac `(mcopy db sb (32+cnt)
       (mstore (db+contractABI$ceil32 cnt) 0w prepared)).vs_memory` >>
     (conj_tac >- simp[ADD_COMM]) >>
     simp_tac (srw_ss()) [ADD_COMM] >>
     irule (SRULE [ADD_COMM] abi_encoder_bytes_write_memory_cong) >>
     fs[window_pure_seq_def]) >>
  fs[window_pure_seq_def]
QED

Theorem window_bytes_sequence:
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) st = (out,final) /\
  eval_operand src s = SOME (n2w sb) /\ mload sb s = n2w cnt /\
  eval_operand dst s = SOME (n2w db) /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at st x) /\
  sb < dimword (:256) /\ cnt+31 < dimword (:256) /\
  db+contractABI$ceil32 cnt < dimword (:256) /\ 32+cnt < dimword (:256) ==>
  ?t. window_seq st final s t /\
    eval_operand out t = SOME (n2w (32+contractABI$ceil32 cnt)) /\
    t.vs_memory = (mcopy db sb (32+cnt) (mstore (db+contractABI$ceil32 cnt) 0w s)).vs_memory /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests /\
    t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx /\
    t.vs_immutables = s.vs_immutables /\ t.vs_outcomes = s.vs_outcomes /\
    t.vs_pending_deletions = s.vs_pending_deletions
Proof
  strip_tac >> drule abi_encode_bytes_trace >> strip_tac >>
  drule_all window_bytes_body_sequence >> strip_tac >>
  rename1 `window_seq st copied s prepared` >>
  drule_all window_bytes_suffix_sequence >> strip_tac >>
  rename1 `window_pure_seq copied final prepared actual` >>
  qexists_tac `actual` >> simp[] >>
  conj_tac >- metis_tac[window_seq_chain, window_pure_seq_def] >>
  fs[window_pure_seq_def]
QED

Theorem window_bytes_concrete_effect[local]:
  cnt <= rounded ==>
  abi_encoder_registered_effect ids [(db,32+rounded)] s
    (mcopy db sb (32+cnt) (mstore (db+rounded) 0w s))
Proof
  strip_tac >> irule abi_encoder_registered_effect_trans >>
  qexists_tac `mstore (db+rounded) 0w s` >>
  conj_tac >- (irule abi_encoder_output_store >> simp[]) >>
  irule abi_encoder_registered_effect_enlarge >>
  qexistsl_tac [`ids`, `[(db,32+cnt)]`] >>
  simp[abi_encoder_registered_output_copy] >> rpt strip_tac >> decide_tac
QED

Theorem window_bytes_effect:
  cnt <= rounded /\
  t.vs_memory = (mcopy db sb (32+cnt) (mstore (db+rounded) 0w s)).vs_memory /\
  t.vs_allocas = s.vs_allocas /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests /\
  t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx /\
  t.vs_immutables = s.vs_immutables /\ t.vs_outcomes = s.vs_outcomes /\
  t.vs_pending_deletions = s.vs_pending_deletions ==>
  abi_encoder_registered_effect ids [(db,32+rounded)] s t
Proof
  strip_tac >> drule window_bytes_concrete_effect >>
  disch_then (qspecl_then [`sb`, `s`, `ids`, `db`] mp_tac) >>
  simp_tac bool_ss [abi_encoder_registered_effect_def,
    abi_encoder_write_observations] >> strip_tac >> asm_rewrite_tac[]
QED

Theorem window_bytes_observed:
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) st = (out,st') /\
  abi_encoder_window_pre ctx func st st' dst src (AbiBytestring maxlen) at av sb cap d s ==>
  ?t. window_strong_result ctx func st st' out at av d s t /\
      (!x. ~not_fresh_at st' x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\
             EVERY (not_fresh_at st') i.inst_outputs) (emitted_insts st st')` by
    metis_tac[window_bytes_output_bounds] >>
  `!i b n. i IN window_alloca_sites func (frag_ids st st') /\
     FLOOKUP s.vs_allocas i = SOME (b,n) ==> n = 32` by
    metis_tac[window_pre_sites] >> pop_assum (mk_asm "sizes") >>
  qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_window_pre_def]) >>
  qpat_x_assum `!inst b sz. _ ==> _` kall_tac >>
  qpat_assum `abi_encoder_window_input _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_window_bytes_iff]) >>
  qpat_x_assum `av = BytesV _` SUBST_ALL_TAC >>
  `LENGTH (enc at (BytesV bs)) = 32+contractABI$ceil32 (LENGTH bs)` by
    metis_tac[abi_encoder_bytes_encoding] >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `LENGTH bs <= contractABI$ceil32 (LENGTH bs)` by
    metis_tac[abi_encoder_ceil32_bounds] >>
  `sb < dimword (:256) /\ LENGTH bs+31 < dimword (:256) /\
   d+contractABI$ceil32 (LENGTH bs) < dimword (:256) /\
   32+LENGTH bs < dimword (:256)` by decide_tac >>
  `mload sb s = n2w (LENGTH bs)` by metis_tac[mem_word_at_eq_mload] >>
  `!x. dst = Var x \/ src = Var x ==> not_fresh_at st x` by metis_tac[] >>
  drule_all window_bytes_sequence >> strip_tac >>
  rename1 `window_seq st st' s actual` >>
  `sb + cap <= d \/ d + LENGTH (enc at (BytesV bs)) <= sb` by
    (qpat_x_assum `venomMemDefs$regions_disjoint _ _` mp_tac >>
     pure_asm_rewrite_tac[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at d (LENGTH (enc at (BytesV bs))) actual.vs_memory =
   enc at (BytesV bs)` by
    (qpat_assum `actual.vs_memory = _` (fn th => rewrite_tac[th]) >>
     irule window_bytes_input_memory >>
     qexistsl_tac [`cap`, `maxlen`] >>
     asm_rewrite_tac[]) >>
  `abi_encoder_registered_effect (window_alloca_sites func (frag_ids st st'))
     [(d,LENGTH (enc at (BytesV bs)))] s actual` by
    (asm_rewrite_tac[] >> irule window_bytes_effect >> simp[] >>
     qexistsl_tac [`LENGTH bs`, `sb`] >> simp[]) >>
  `abi_encoder_extend_sim ctx func s
    (actual with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule window_seq_extend_sim >> simp[] >> qexists_tac `st` >> simp[]) >>
  `!x. ~not_fresh_at st' x ==>
       lookup_var x (actual with vs_inst_idx := LENGTH st'.cs_current_insts) =
       lookup_var x s` by
    (`run_inst_seq (emitted_insts st st') s = OK actual` by
       gvs[window_seq_def] >>
     drule abi_window_seq_high_vars >>
     disch_then (qspec_then `st'` mp_tac) >> simp[lookup_var_def]) >>
  qexists_tac `actual with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  (conj_tac >- (
  (* Package the concrete sequence without reopening instruction semantics. *)
  `alloca_inv actual` by (irule alloca_inv_fields >> qexists_tac `s` >> simp[]) >>
  `alloca_room ctx func actual` by
    (irule alloca_room_fields >> qexists_tac `s` >> simp[]) >>
  `st'.cs_current_bb = st.cs_current_bb` by metis_tac[window_seq_def] >>
  qpat_x_assum `actual.vs_memory = _` kall_tac >>
  qmatch_goalsub_abbrev_tac `window_strong_result _ _ _ _ _ _ _ _ _ final` >>
  `final.vs_allocas = s.vs_allocas /\ final.vs_alloca_next = s.vs_alloca_next` by
    simp[Abbr `final`] >>
  `alloca_inv final` by (irule alloca_inv_fields >> qexists_tac `s` >> simp[]) >>
  `alloca_room ctx func final` by
    (irule alloca_room_fields >> qexists_tac `s` >> simp[Abbr `final`]) >>
  `eval_operand out final = eval_operand out actual` by
    (Cases_on `out` >> simp_tac (srw_ss())
      [eval_operand_def, lookup_var_def, Abbr `final`]) >>
  `!x. lookup_var x final = lookup_var x actual` by
    simp[lookup_var_def, Abbr `final`] >>
  `abi_encoder_registered_effect (window_alloca_sites func (frag_ids st st'))
     [(d,LENGTH (enc at (BytesV bs)))] s final` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `actual` >>
     simp[Abbr `final`, abi_encoder_registered_inst_idx]) >>
  `abi_encoder_registered_effect (frag_ids st st')
     [(d,LENGTH (enc at (BytesV bs)))] s final` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`window_alloca_sites func (frag_ids st st')`,
       `[(d,LENGTH (enc at (BytesV bs))) ]`] >>
     simp[window_alloca_sites_subset]) >>
  `mem_bytes_at d (LENGTH (enc at (BytesV bs))) final.vs_memory =
    enc at (BytesV bs)` by
    (qpat_assum `mem_bytes_at _ _ actual.vs_memory = _` mp_tac >>
     simp_tac (srw_ss()) [Abbr `final`]) >>
  `window_alloca_growth s final` by
    (simp[window_alloca_growth_def] >> metis_tac[optionTheory.NOT_SOME_NONE]) >>
  `!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
     lookup_var x final = SOME w` by metis_tac[window_seq_def] >>
  `~final.vs_halted /\ final.vs_current_bb = st'.cs_current_bb /\
   final.vs_inst_idx = LENGTH st'.cs_current_insts` by simp[Abbr `final`] >>
  `abi_decode_sim ctx func s final` by metis_tac[abi_encoder_extend_sim_sim] >>
  simp_tac bool_ss [window_strong_result_def, abi_encoder_window_result_def] >>
  asm_rewrite_tac[] >> (conj_tac >- asm "sizes" ACCEPT_TAC) >>
  simp[Abbr `final`] >> metis_tac[window_seq_labels])) >> simp[]
QED

Theorem window_bytes_contract:
  window_strong_contract (AbiBytestring maxlen)
Proof
  rw[window_strong_contract_def] >> metis_tac[window_bytes_observed]
QED

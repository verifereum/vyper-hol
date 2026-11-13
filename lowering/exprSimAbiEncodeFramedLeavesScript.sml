Theory exprSimAbiEncodeFramedLeaves
Ancestors
  exprSimAbiEncodeExecFrame exprSimAbiEncodeMemoryLength abiEncoderWindowLeaves abiEncoderWindowBytes
  venomInstProofs1 rich_list abiEncoderWindowSequence abiEncoderRounding abiEncoderBytes
  abiEncoderWindowContract abiEncoderLeaves abiEncoderWrites
  abiEncoderReentryLeaves moduleLoweringProps abiEncoderMemory
  abiEncoder abiEncoderOpenInput abiEncoderInput contractABI valueEncoding
  abiEncoderPrimitiveEffect abiEncoderExtendSim abiEncoderWindow
  abiEncoderRegisteredEffect valueEncodingProofs valueEncodingProps
  emitHelperProps exprLoweringProps localPtrsProps
  emitHelper compileEnv venomState venomExecSemantics venomInst words list
  abiEncoderWindowLookup exprSimAbiEncodeSemantic stmtSimLogExecFields
  valueEncodingDefs

Theorem abi_encode_framed_copy_observed:
  compile_abi_encode_to_buf dst src (AbiCopy sz) st = (out,st') /\
  abi_encoder_window_pre ctx func st st' dst src (AbiCopy sz) at av sb cap d s ==>
  ?t. window_strong_result ctx func st st' out at av d s t /\
      abi_encode_exec_frame func s t
Proof
  strip_tac >> drule_all window_copy_strong_endpoint >> strip_tac >>
  qexists_tac `(mcopy d sb sz s) with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp[]
QED

Theorem abi_encode_framed_copy_contract:
  abi_encode_framed_contract (AbiCopy sz)
Proof
  rw[abi_encode_framed_contract_def] >> metis_tac[abi_encode_framed_copy_observed]
QED

Theorem abi_encode_framed_empty_observed:
  compile_abi_encode_to_buf dst src (AbiComplex []) st = (out,st') /\
  abi_encoder_window_pre ctx func st st' dst src (AbiComplex []) at av sb cap d s ==>
  ?t. window_strong_result ctx func st st' out at av d s t /\
      abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `!i b n. i IN window_alloca_sites func (frag_ids st st') /\
     FLOOKUP s.vs_allocas i = SOME (b,n) ==> n = 32` by
    metis_tac[window_pre_sites] >>
  pop_assum (mk_asm "sizes") >>
  qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_window_pre_def]) >>
  qpat_x_assum `!inst b sz. _ ==> _` kall_tac >>
  gvs[Once compile_abi_encode_child_def, comp_return_def] >>
  `enc at av = []` by
    (fs[abi_encoder_window_complex_iff, abi_encoder_tuple_type_def,
       abi_encoder_member_span_def, enc_def, LET_THM, REV_DEF]) >>
  qexists_tac `s` >> simp[] >>
  simp[window_strong_result_def, abi_encoder_window_result_def,
    mem_bytes_at_def, eval_operand_def, abi_encoder_registered_effect_refl,
    abi_encoder_extend_sim_refl, abi_encoder_extend_sim_sim,
    window_alloca_growth_def] >>
  (conj_tac >- metis_tac[optionTheory.NOT_SOME_NONE]) >>
  asm "sizes" ACCEPT_TAC
QED

Theorem abi_encode_framed_empty_contract:
  abi_encode_framed_contract (AbiComplex [])
Proof
  rw[abi_encode_framed_contract_def] >> metis_tac[abi_encode_framed_empty_observed]
QED

Theorem abi_encode_framed_word_observed:
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,st') /\
  abi_encoder_window_pre ctx func st st' dst src AbiPrimWord at av sb cap d s ==>
  ?t. window_strong_result ctx func st st' out at av d s t /\
      abi_encode_exec_frame func s t
Proof
  strip_tac >> drule_all window_word_strong_endpoint >> strip_tac >>
  qexists_tac `(mstore d (mload sb s)
    (update_var (STRING #"%" (toString st.cs_next_var)) (mload sb s) s))
    with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp[] >> irule abi_encode_exec_frame_trans >>
  qexists_tac `update_var (STRING #"%" (toString st.cs_next_var)) (mload sb s) s` >>
  conj_tac >-
    simp_tac (srw_ss()) [abi_encode_exec_frame_def, pending_alloca_size_def,
      update_var_def, abi_encode_semantic_obs_def] >>
  simp[]
QED

Theorem abi_encode_framed_word_contract:
  abi_encode_framed_contract AbiPrimWord
Proof
  rw[abi_encode_framed_contract_def] >> metis_tac[abi_encode_framed_word_observed]
QED

Theorem abi_encode_leaf_sequence_semantic:
  run_inst_seq code s = OK t /\
  EVERY (\i. MEM i.inst_opcode [ADD;AND;NOT;MLOAD;MSTORE;MCOPY]) code ==>
  abi_encode_semantic_obs t = abi_encode_semantic_obs s
Proof
  strip_tac >> irule abi_encode_semantic_sequence >>
  goal_assum (drule_at Any) >>
  gvs[EVERY_MEM, log_encode_safe_opcode_def] >> metis_tac[]
QED

Theorem abi_encode_leaf_sequence_fmp:
  run_inst_seq code s = OK t /\
  EVERY (\i. MEM i.inst_opcode [ADD;AND;NOT;MLOAD;MSTORE;MCOPY]) code ==>
  t.vs_fmp = s.vs_fmp
Proof
  strip_tac >> irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_fmp`
    run_inst_seq_preserves_field)) >>
  qexists_tac `code` >> simp[] >> rpt strip_tac >>
  irule step_inst_base_preserves_fmp_ordinary >>
  qexists_tac `i` >> simp[] >>
  fs[EVERY_MEM] >> first_x_assum drule >>
  simp[is_terminator_def, is_alloca_op_def, is_ext_call_op_def] >>
  rpt strip_tac >> gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def]
QED

Theorem abi_encode_bytes_opcodes:
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) st = (out,st') ==>
  EVERY (\i. MEM i.inst_opcode [ADD;AND;NOT;MLOAD;MSTORE;MCOPY]) (emitted_insts st st')
Proof
  simp[Once compile_abi_encode_child_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_encode_framed_bytes_sequence:
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) st = (out,en) /\
  abi_encoder_window_pre ctx func st en dst src (AbiBytestring maxlen) at av sb cap d s ==>
  ?raw. window_seq st en s raw /\
    window_strong_result ctx func st en out at av d s
      (raw with vs_inst_idx := LENGTH en.cs_current_insts) /\
    abi_encode_exec_frame func s (raw with vs_inst_idx := LENGTH en.cs_current_insts)
Proof
  strip_tac >> drule_all window_bytes_strong_sequence >> strip_tac >>
  rename1 `window_seq st en s raw` >>
  `EVERY (\i. MEM i.inst_opcode [ADD;AND;NOT;MLOAD;MSTORE;MCOPY])
     (emitted_insts st en)` by metis_tac[abi_encode_bytes_opcodes] >>
  `run_inst_seq (emitted_insts st en) s = OK raw` by fs[window_seq_def] >>
  `abi_encode_semantic_obs raw = abi_encode_semantic_obs s` by
    metis_tac[abi_encode_leaf_sequence_semantic] >>
  `raw.vs_fmp = s.vs_fmp` by metis_tac[abi_encode_leaf_sequence_fmp] >>
  `LENGTH s.vs_memory <= LENGTH raw.vs_memory` by
    (irule abi_encode_leaf_sequence_memory_length >>
     qexists_tac `emitted_insts st en` >> simp[] >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  qexists_tac `raw` >> simp[] >>
  qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_window_pre_def]) >>
  qpat_assum `abi_encoder_window_input _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_window_bytes_iff]) >>
  `LENGTH (enc at av) = 32+contractABI$ceil32 (LENGTH bs)` by
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
  `t = raw` by fs[window_seq_def] >>
  qpat_x_assum `t = raw` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `t.vs_memory = _` kall_tac >>
  simp[abi_encode_exec_frame_def, pending_alloca_size_def]
QED

Theorem abi_encode_framed_bytes_observed:
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) st = (out,st') /\
  abi_encoder_window_pre ctx func st st' dst src (AbiBytestring maxlen) at av sb cap d s ==>
  ?t. window_strong_result ctx func st st' out at av d s t /\
      abi_encode_exec_frame func s t
Proof
  strip_tac >> drule_all abi_encode_framed_bytes_sequence >> strip_tac >>
  rename1 `window_seq st st' s raw` >>
  qexists_tac `raw with vs_inst_idx := LENGTH st'.cs_current_insts` >> simp[]
QED

Theorem abi_encode_framed_bytes_contract:
  abi_encode_framed_contract (AbiBytestring maxlen)
Proof
  rw[abi_encode_framed_contract_def] >> metis_tac[abi_encode_framed_bytes_observed]
QED

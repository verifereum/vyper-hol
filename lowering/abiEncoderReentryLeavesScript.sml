(* Word and fixed-copy encoders under enclosing variable freshness. *)
Theory abiEncoderReentryLeaves
Ancestors
  abiEncoderInput abiEncoderBytes abiEncoderMemory abiEncoderLeafRaw
  abiDecoderArrayHeader abiDecoderReentry abiDecoderContract abiDecoderGuards
  abiEncoder emitHelperProps exprLoweringProps compileEnv emitHelper
  valueEncoding valueEncodingProps contractABI venomState venomExecSemantics
  venomInst words list arithmetic ssaOperandFrame abiBytestringCode abiDecoderReentryAddress

Theorem abi_encode_word_trace:
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,st') ==>
  out = Lit 32w /\ ?value loaded_st.
    emit_op MLOAD [src] st = (value,loaded_st) /\
    emit_void MSTORE [dst;value] loaded_st = ((),st')
Proof
  simp_tac bool_ss [Once compile_abi_encode_child_def, compile_abi_encode_static_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MLOAD [src] st = (value,loaded_st)` >>
  qexistsl_tac [`value`, `loaded_st`] >> simp[]
QED

Theorem abi_encoder_store_memory:
  s.vs_memory = t.vs_memory ==>
  (mstore db w s).vs_memory = (mstore db w t).vs_memory
Proof
  simp[mstore_def, write_memory_with_expansion_def]
QED

Theorem abi_encode_word_reentry:
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,st') /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w db) /\
  abi_decoder_operand_live st.cs_next_var dst /\
  sb < dimword (:256) /\ db < dimword (:256) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. run_inst_seq (emitted_insts st st') s = OK actual /\ inst_extends st st' /\
    eval_operand out actual = SOME 32w /\ fresh_vars_wrt limit_st actual /\
    mem_bytes_at db 32 actual.vs_memory = mem_bytes_at sb 32 s.vs_memory /\
    abi_decode_frame db 32 s actual /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  strip_tac >>
  `compile_abi_encode_static dst src st = (out,st')` by
    fs[Once compile_abi_encode_child_def] >>
  drule compile_abi_encode_static_code >> strip_tac >>
  `dst <> Var (STRING #"%" (toString st.cs_next_var))` by
    (mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `op` |-> `dst`, `num_names` |-> `1`]
      abi_encoder_live_names) >> simp[compiler_var_names_def, GENLIST]) >>
  drule_all compile_abi_encode_static_execution >>
  disch_then (fn th => ASSUM_LIST (fn asl =>
    strip_assume_tac (SIMP_RULE (srw_ss()) (w2n_n2w::asl) th))) >>
  qmatch_asmsub_abbrev_tac `OK (mstore db (mload sb s) loaded)` >>
  mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `t` |-> `loaded:venom_state`,
    `w` |-> `mload sb s`] abi_decoder_register_update) >>
  impl_tac >- (simp[Abbr`loaded`, update_var_def] >> decide_tac) >> strip_tac >>
  `abi_decode_frame db 32 s (mstore db (mload sb s) loaded)` by
    (mp_tac (Q.INST [`d` |-> `db`, `w` |-> `mload sb s`] abi_decode_mstore_frame) >>
     simp[abi_decode_frame_def, Abbr`loaded`, mstore_update_var, update_var_def]) >>
  qexists_tac `mstore db (mload sb s) loaded` >>
  asm_simp_tac (srw_ss()) [inst_extends_def, abi_encoder_word_window,
    mstore_mem_word_at_same, mem_word_at_eq_mload, eval_operand_lit,
    eval_operand_mstore_eq, fresh_vars_wrt_mstore] >>
  simp[Abbr`loaded`, update_var_def]
QED

Theorem abi_encode_copy_reentry:
  compile_abi_encode_to_buf dst src (AbiCopy sz) st = (out,st') /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w db) /\
  sb < dimword (:256) /\ db < dimword (:256) /\ sz < dimword (:256) /\
  fresh_vars_wrt limit_st s ==>
  ?actual. run_inst_seq (emitted_insts st st') s = OK actual /\ inst_extends st st' /\
    eval_operand out actual = SOME (n2w sz) /\ fresh_vars_wrt limit_st actual /\
    mem_bytes_at db sz actual.vs_memory = mem_bytes_at sb sz s.vs_memory /\
    abi_decode_frame db sz s actual /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op actual = SOME w)
Proof
  strip_tac >> drule_all compile_abi_copy_execution >>
  disch_then (fn th => ASSUM_LIST (fn asl =>
    strip_assume_tac (SIMP_RULE (srw_ss()) (w2n_n2w::asl) th))) >>
  `abi_decode_frame db sz s (mcopy db sb sz s)` by
    (simp_tac bool_ss [abi_decode_frame_def] >> conj_tac
     >- (rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> asm_simp_tac bool_ss []) >>
     simp[]) >>
  `fresh_vars_wrt limit_st (mcopy db sb sz s)` by
    fs[fresh_vars_wrt_def, mcopy_def, write_memory_with_expansion_def] >>
  qexists_tac `mcopy db sb sz s` >>
  asm_simp_tac (srw_ss()) [mcopy_mem_bytes_at_same, abi_encoder_copy_eval,
    eval_operand_def, inst_extends_def]
QED

Theorem abi_encoder_word_input_reentry:
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,st') /\
  abi_encoder_input AbiPrimWord at av sb cap s.vs_memory /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w db) /\
  abi_decoder_operand_live st.cs_next_var dst /\
  sb < dimword (:256) /\ db < dimword (:256) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. run_inst_seq (emitted_insts st st') s = OK actual /\ inst_extends st st' /\
    mem_bytes_at db (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\ fresh_vars_wrt limit_st actual /\
    abi_decode_frame db (LENGTH (enc at av)) s actual /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  strip_tac >> qpat_assum `abi_encoder_input _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o REWRITE_RULE [abi_encoder_input_word_iff]) >>
  `LENGTH (enc at av) = 32` by (drule_all (cj 1 enc_has_static_length) >> simp[]) >>
  drule_all abi_encode_word_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK actual` >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) []
QED

Theorem abi_encoder_copy_input_reentry:
  compile_abi_encode_to_buf dst src (AbiCopy sz) st = (out,st') /\
  abi_encoder_input (AbiCopy sz) at av sb cap s.vs_memory /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w db) /\
  sb < dimword (:256) /\ db < dimword (:256) /\ sz < dimword (:256) /\
  fresh_vars_wrt limit_st s ==>
  ?actual. run_inst_seq (emitted_insts st st') s = OK actual /\ inst_extends st st' /\
    mem_bytes_at db (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\ fresh_vars_wrt limit_st actual /\
    abi_decode_frame db (LENGTH (enc at av)) s actual /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op actual = SOME w)
Proof
  strip_tac >> qpat_assum `abi_encoder_input _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o REWRITE_RULE [abi_encoder_input_copy_iff]) >>
  `LENGTH (enc at av) = sz` by (drule_all (cj 1 enc_has_static_length) >> simp[]) >>
  drule_all abi_encode_copy_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK actual` >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

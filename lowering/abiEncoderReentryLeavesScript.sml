(* Word and fixed-copy encoders under enclosing variable freshness. *)
Theory abiEncoderReentryLeaves
Ancestors
  abiEncoderLeaves abiEncoderInput abiEncoderWrites abiEncoderBytes abiEncoderBytesPrefix
  abiEncoderMemory abiBuiltinPrefix abiDecoderArrayHeader abiDecoderDynamicLoopSetup
  abiDecoderReentry abiDecoderContract abiDecoderGuards abiEncoder emitHelperProps
  exprLoweringProps compileEnv emitHelper valueEncoding valueEncodingProps contractABI
  venomState venomExecSemantics venomInst words list arithmetic

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
  strip_tac >> drule abi_encode_word_trace >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  `loaded_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_builtin_emit_load >> strip_tac >>
  rename1 `abi_builtin_prefix st loaded_st limit_st s loaded` >>
  `eval_operand value loaded = SOME (mload sb s)` by fs[w2n_n2w] >>
  `eval_operand dst loaded = SOME (n2w db)` by
    (mp_tac (Q.INST [`st'` |-> `loaded_st`, `t` |-> `loaded:venom_state`,
      `op` |-> `dst`, `w` |-> `n2w db:bytes32`] abi_encoder_prefix_eval) >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  mp_tac (Q.INST [`ptr_op` |-> `dst`, `value_op` |-> `value`, `p` |-> `db`,
    `w` |-> `mload sb s`, `st` |-> `loaded_st`, `s` |-> `loaded:venom_state`]
    abi_encoder_emit_store) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qabbrev_tac `actual = mstore db (mload sb s) loaded` >>
  `run_inst_seq (emitted_insts st st') s = OK actual /\ inst_extends st st'` by
    (mp_tac (Q.INST [`st1` |-> `loaded_st`, `st2` |-> `st'`, `s1` |-> `loaded:venom_state`,
      `s2` |-> `actual:venom_state`] abi_decode_sequence_chain) >> asm_simp_tac bool_ss [Abbr`actual`]) >>
  `actual.vs_memory = (mstore db (mload sb s) s).vs_memory` by
    (simp_tac bool_ss [Abbr`actual`] >> irule abi_encoder_store_memory >> asm_simp_tac bool_ss []) >>
  `abi_decode_frame db 32 s actual` by
    (mp_tac (Q.INST [`t` |-> `mstore db (mload sb s) s`, `u` |-> `actual:venom_state`, `sz` |-> `32`]
      abi_encoder_frame_memory) >>
     asm_simp_tac (srw_ss()) [abi_decode_mstore_frame, Abbr`actual`]) >>
  `mem_bytes_at db 32 actual.vs_memory = mem_bytes_at sb 32 s.vs_memory` by
    (simp_tac bool_ss [abi_encoder_word_window] >>
     asm_simp_tac (srw_ss()) [mstore_mem_word_at_same, GSYM mem_word_at_eq_mload]) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [Abbr`actual`, eval_operand_def] >>
  rpt strip_tac >> irule eval_operand_mstore >>
  first_x_assum irule >> asm_simp_tac bool_ss []
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
  strip_tac >> drule abi_encode_copy_code >> strip_tac >>
  mp_tac (Q.INST [`len` |-> `Lit (n2w sz)`, `cnt` |-> `sz`] abi_encoder_emit_copy) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  `abi_decode_frame db sz s (mcopy db sb sz s)` by
    (simp_tac bool_ss [abi_decode_frame_def] >> conj_tac
     >- (rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> asm_simp_tac bool_ss []) >>
     simp[]) >>
  qexists_tac `mcopy db sb sz s` >>
  asm_simp_tac (srw_ss()) [mcopy_mem_bytes_at_same, abi_encoder_copy_eval, eval_operand_def]
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

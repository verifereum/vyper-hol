(* A real cursor store followed by its reload, under enclosing freshness. *)
Theory abiEncoderCursorStoreLoad
Ancestors
  abiEncoderWrites abiEncoderReentryLeaves abiEncoderChildSuffix abiEncoderMemory abiBuiltinPrefix
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderArrayHeader abiDecoderContract abiDecoderGuards
  emitHelperProps exprLoweringProps compileEnv emitHelper valueEncoding valueEncodingProps
  venomState venomExecSemantics venomMemProps words list arithmetic

Theorem abi_encoder_cursor_store_load:
  emit_void MSTORE [cursor_op;value_op] st = ((),stored_st) /\
  emit_op MLOAD [cursor_op] stored_st = (out,final) /\
  eval_operand cursor_op s = SOME (n2w slot) /\ eval_operand value_op s = SOME w /\
  abi_decoder_operand_live st.cs_next_var cursor_op /\ slot < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. run_inst_seq (emitted_insts st final) s = OK actual /\ inst_extends st final /\
    eval_operand out actual = SOME w /\ mload slot actual = w /\ fresh_vars_wrt limit_st actual /\
    actual.vs_memory = (mstore slot w s).vs_memory /\ abi_decode_frame slot 32 s actual /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\
    (!op w'. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w' ==>
      eval_operand op actual = SOME w')
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule emitted_insts_emit_void >> strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule_all abi_encoder_emit_store >> strip_tac >>
  qabbrev_tac `stored = mstore slot w s` >>
  mp_tac (Q.INST [`src` |-> `cursor_op`, `p` |-> `n2w slot:bytes32`, `st` |-> `stored_st`,
    `st'` |-> `final`, `s` |-> `stored:venom_state`] abi_builtin_emit_load) >>
  impl_tac >- asm_simp_tac (srw_ss()) [Abbr`stored`, eval_operand_mstore] >> strip_tac >>
  rename1 `abi_builtin_prefix stored_st final limit_st stored actual` >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `run_inst_seq (emitted_insts st final) s = OK actual /\ inst_extends st final` by
    (mp_tac (Q.INST [`st1` |-> `stored_st`, `st2` |-> `final`,
      `s1` |-> `stored:venom_state`, `s2` |-> `actual:venom_state`] abi_decode_sequence_chain) >>
     asm_simp_tac bool_ss [Abbr`stored`]) >>
  `abi_decode_frame slot 32 s actual` by
    (mp_tac (Q.INST [`t` |-> `stored:venom_state`, `u` |-> `actual:venom_state`,
      `sz` |-> `32`, `db` |-> `slot:num`] abi_encoder_frame_memory) >>
     asm_simp_tac (srw_ss()) [Abbr`stored`, abi_decode_mstore_frame]) >>
  `mload slot actual = mload slot stored` by asm_simp_tac bool_ss [mload_def] >>
  `mload slot actual = w` by fs[Abbr`stored`, mload_mstore_same] >>
  qexists_tac `actual` >>
  asm_simp_tac (srw_ss()) [Abbr`stored`, w2n_n2w, mload_mstore_same] >>
  rpt strip_tac >> first_x_assum irule >> asm_simp_tac (srw_ss()) [eval_operand_mstore] >>
  irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []
QED

(* The parent array prefix copies its count under the enclosing freshness bound. *)
Theory abiEncoderArrayCountCopy
Ancestors
  abiEncoderWrites abiEncoderReentryLeaves abiEncoderMemory abiEncoderBytesPrefix abiBuiltinPrefix
  abiDecoderArrayHeader abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderContract abiDecoderGuards
  emitHelperProps exprLoweringProps compileEnv emitHelper valueEncoding valueEncodingProps
  venomState venomExecSemantics words list arithmetic

Theorem abi_encoder_array_count_copy_sequence:
  abi_decode_array_header dst src MLOAD st = (cnt,st') /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w db) /\
  abi_decoder_operand_live st.cs_next_var dst /\
  sb < dimword (:256) /\ db < dimword (:256) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. run_inst_seq (emitted_insts st st') s = OK actual /\ inst_extends st st' /\
    eval_operand cnt actual = SOME (mload sb s) /\ mem_word_at db actual.vs_memory = mload sb s /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame db 32 s actual /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  simp_tac bool_ss [abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, LET_THM] >> pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MLOAD [src] st = (cnt,loaded_st)` >>
  rename1 `emit_void MSTORE [dst;cnt] loaded_st = ((),ready)` >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  `loaded_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_builtin_emit_load >> strip_tac >>
  rename1 `abi_builtin_prefix st loaded_st limit_st s loaded` >>
  `eval_operand cnt loaded = SOME (mload sb s)` by fs[w2n_n2w] >>
  `eval_operand dst loaded = SOME (n2w db)` by
    (mp_tac (Q.INST [`st'` |-> `loaded_st`, `t` |-> `loaded:venom_state`,
      `op` |-> `dst`, `w` |-> `n2w db:bytes32`] abi_encoder_prefix_eval) >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  mp_tac (Q.INST [`ptr_op` |-> `dst`, `value_op` |-> `cnt`, `p` |-> `db`,
    `w` |-> `mload sb s`, `st` |-> `loaded_st`, `st'` |-> `ready`, `s` |-> `loaded:venom_state`]
    abi_encoder_emit_store) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qabbrev_tac `actual = mstore db (mload sb s) loaded` >>
  `run_inst_seq (emitted_insts st ready) s = OK actual /\ inst_extends st ready` by
    (mp_tac (Q.INST [`st1` |-> `loaded_st`, `st2` |-> `ready`, `s1` |-> `loaded:venom_state`,
      `s2` |-> `actual:venom_state`] abi_decode_sequence_chain) >> asm_simp_tac bool_ss [Abbr`actual`]) >>
  `actual.vs_memory = (mstore db (mload sb s) s).vs_memory` by
    (simp_tac bool_ss [Abbr`actual`] >> irule abi_encoder_store_memory >> asm_simp_tac bool_ss []) >>
  `abi_decode_frame db 32 s actual` by
    (mp_tac (Q.INST [`t` |-> `mstore db (mload sb s) s`, `u` |-> `actual:venom_state`, `sz` |-> `32`]
      abi_encoder_frame_memory) >> asm_simp_tac (srw_ss()) [abi_decode_mstore_frame, Abbr`actual`]) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss())
    [Abbr`actual`, mstore_mem_word_at_same, eval_operand_mstore] >>
  rpt strip_tac >> first_x_assum irule >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_COUNT_COPY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder count copy not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayCountCopy");

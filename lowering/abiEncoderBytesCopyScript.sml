(* Execute the actual zero-store, copy-length ADD and MCOPY bytes phase. *)
Theory abiEncoderBytesCopy
Ancestors
  abiEncoderBytesCode abiEncoderWrites abiBuiltinPrefix abiDecoderDynamicLoopSetup
  abiDecoderReentry abiDecoderGuards abiDecoderContract emitHelperProps exprLoweringProps
  emitHelper compileEnv venomState venomExecSemantics venomInst words list arithmetic

Theorem abi_encoder_copy_eval:
  eval_operand op (mcopy db sb cnt s) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def, mcopy_def, write_memory_with_expansion_def]
QED

Theorem abi_encoder_copy_memory:
  s.vs_memory = t.vs_memory ==>
  (mcopy db sb cnt s).vs_memory = (mcopy db sb cnt t).vs_memory
Proof
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem abi_encode_bytes_copy_sequence:
  abi_encode_bytes_copy dst src len lastptr st = ((),st') /\
  eval_operand dst s = SOME (n2w db) /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand len s = SOME (n2w cnt) /\ eval_operand lastptr s = SOME (n2w (db+rounded)) /\
  db+rounded < dimword (:256) /\ sb < dimword (:256) /\ 32+cnt < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var src /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. run_inst_seq (emitted_insts st st') s = OK actual /\
    actual.vs_memory = (mcopy db sb (32+cnt) (mstore (db+rounded) 0w s)).vs_memory /\
    fresh_vars_wrt limit_st actual /\ inst_extends st st' /\
    actual.vs_call_ctx = s.vs_call_ctx /\ actual.vs_data_section = s.vs_data_section /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  simp_tac bool_ss [abi_encode_bytes_copy_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_void MSTORE [lastptr;Lit 0w] st = ((),c1)` >>
  rename1 `emit_op ADD [Lit 32w;len] c1 = (copylen,c2)` >>
  rename1 `emit_void MCOPY [dst;src;copylen] c2 = ((),end_st)` >>
  imp_res_tac emitted_insts_emit_void >> imp_res_tac emitted_insts_emit_op >>
  `db < dimword (:256) /\ c2.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`ptr_op` |-> `lastptr`, `value_op` |-> `Lit 0w`, `p` |-> `db+rounded`,
    `w` |-> `0w:bytes32`, `st'` |-> `c1`] abi_encoder_emit_store) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  qabbrev_tac `stored = mstore (db+rounded) 0w s` >>
  mp_tac (Q.INST [`lhs` |-> `Lit 32w`, `rhs` |-> `len`, `out` |-> `copylen`,
    `a` |-> `32w:bytes32`, `b` |-> `n2w cnt:bytes32`, `st` |-> `c1`, `st'` |-> `c2`,
    `s` |-> `stored:venom_state`] abi_builtin_emit_add) >>
  impl_tac >- asm_simp_tac (srw_ss()) [Abbr`stored`, eval_operand_def, eval_operand_mstore] >>
  strip_tac >> rename1 `abi_builtin_prefix c1 c2 limit_st stored prepared` >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `eval_operand dst prepared = SOME (n2w db) /\ eval_operand src prepared = SOME (n2w sb)` by
    (conj_tac >> first_x_assum irule >> asm_simp_tac (srw_ss()) [Abbr`stored`, eval_operand_mstore]) >>
  `eval_operand copylen prepared = SOME (n2w (32+cnt))` by fs[word_add_n2w] >>
  mp_tac (Q.INST [`dst` |-> `dst`, `src` |-> `src`, `len` |-> `copylen`,
    `cnt` |-> `32+cnt`, `st` |-> `c2`, `st'` |-> `end_st`, `s` |-> `prepared:venom_state`]
    abi_encoder_emit_copy) >> impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  `run_inst_seq (emitted_insts st c2) s = OK prepared /\ inst_extends st c2` by
    (mp_tac (Q.INST [`st1` |-> `c1`, `st2` |-> `c2`, `s1` |-> `stored:venom_state`,
      `s2` |-> `prepared:venom_state`] abi_decode_sequence_chain) >> asm_simp_tac bool_ss [Abbr`stored`]) >>
  qexists_tac `mcopy db sb (32+cnt) prepared` >>
  asm_simp_tac bool_ss [abi_encoder_copy_eval] >> rpt conj_tac
  >- (irule run_inst_seq_compose_ok >> qexistsl_tac [`prepared`, `c2`] >> asm_simp_tac bool_ss [])
  >- (simp_tac bool_ss [ADD_COMM] >> irule abi_encoder_copy_memory >> asm_simp_tac bool_ss [])
  >- (irule inst_extends_trans >> qexists_tac `c2` >> asm_simp_tac bool_ss []) >>
  asm_simp_tac (srw_ss()) [abi_encoder_write_observations, Abbr`stored`] >>
  rpt strip_tac >> first_x_assum irule >> asm_simp_tac (srw_ss()) [eval_operand_mstore]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_BYTES_COPY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder bytes copy not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderBytesCopy");

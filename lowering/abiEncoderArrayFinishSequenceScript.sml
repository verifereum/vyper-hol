(* Execute the real parent cursor MLOAD/ADD/MSTORE/MLOAD bookkeeping. *)
Theory abiEncoderArrayFinishSequence
Ancestors
  abiEncoderArrayPhases abiEncoderArrayScalarCode abiEncoderCursorStoreLoad
  abiEncoderBytesPrefix abiBuiltinPrefix abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecoderFrameCompose abiDecoderArrayHeader abiDecoderContract abiDecoderGuards
  emitHelperProps exprLoweringProps compileEnv emitHelper venomState venomExecSemantics
  words list arithmetic

Theorem abi_encode_array_finish_trace:
  abi_encode_array_finish parent_ptr size_op st = (out,final) ==>
  ?old c1 next c2 c3.
    emit_op MLOAD [parent_ptr] st = (old,c1) /\
    emit_op ADD [old;size_op] c1 = (next,c2) /\
    emit_void MSTORE [parent_ptr;next] c2 = ((),c3) /\
    emit_op MLOAD [parent_ptr] c3 = (out,final)
Proof
  simp_tac bool_ss [abi_encode_array_finish_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op MLOAD [parent_ptr] st = (old,c1)` >>
  rename1 `emit_op ADD [old;size_op] c1 = (next,c2)` >>
  rename1 `emit_void MSTORE [parent_ptr;next] c2 = ((),c3)` >>
  qexistsl_tac [`old`, `c1`, `next`, `c2`, `c3`] >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_cursor_sum:
  emit_op MLOAD [cursor_op] st = (old,c1) /\ emit_op ADD [old;size_op] c1 = (next,c2) /\
  eval_operand cursor_op s = SOME (n2w slot) /\ mload slot s = old_word /\
  eval_operand size_op s = SOME size_word /\ abi_decoder_operand_live st.cs_next_var size_op /\
  slot < dimword (:256) /\ c2.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?prepared. eval_operand next prepared = SOME (old_word+size_word) /\
    abi_builtin_prefix st c2 limit_st s prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> imp_res_tac emitted_insts_emit_op >>
  `c1.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= c1.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`src` |-> `cursor_op`, `out` |-> `old`, `p` |-> `n2w slot:bytes32`,
    `st'` |-> `c1`] abi_builtin_emit_load) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_builtin_prefix st c1 limit_st s loaded` >>
  `eval_operand old loaded = SOME old_word /\ fresh_vars_wrt limit_st loaded` by
    fs[abi_builtin_prefix_def, w2n_n2w] >>
  `eval_operand size_op loaded = SOME size_word` by
    (mp_tac (Q.INST [`op` |-> `size_op`, `w` |-> `size_word:bytes32`,
      `st'` |-> `c1`, `t` |-> `loaded:venom_state`] abi_encoder_prefix_eval) >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`lhs` |-> `old`, `rhs` |-> `size_op`, `out` |-> `next`,
    `a` |-> `old_word:bytes32`, `b` |-> `size_word:bytes32`,
    `st` |-> `c1`, `st'` |-> `c2`, `s` |-> `loaded:venom_state`] abi_builtin_emit_add) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_builtin_prefix c1 c2 limit_st loaded prepared` >>
  qexists_tac `prepared` >> asm_simp_tac bool_ss [] >>
  irule abi_builtin_prefix_chain >> qexistsl_tac [`c1`, `loaded`] >> asm_simp_tac bool_ss []
QED

Theorem abi_encode_array_finish_sequence:
  abi_encode_array_finish parent_ptr size_op st = (out,final) /\
  eval_operand parent_ptr initial = SOME (n2w slot) /\ mload slot initial = old_word /\
  eval_operand size_op initial = SOME size_word /\
  abi_decoder_operand_live st.cs_next_var parent_ptr /\ abi_decoder_operand_live st.cs_next_var size_op /\
  slot < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\ inst_extends st final /\
    eval_operand out actual = SOME (old_word+size_word) /\ mload slot actual = old_word+size_word /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame slot 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> drule abi_encode_array_finish_trace >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  `c2.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= c2.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`cursor_op` |-> `parent_ptr`, `s` |-> `initial:venom_state`] abi_encoder_cursor_sum) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `eval_operand parent_ptr prepared = SOME (n2w slot)` by
    (mp_tac (Q.INST [`op` |-> `parent_ptr`, `w` |-> `n2w slot:bytes32`, `st'` |-> `c2`,
      `s` |-> `initial:venom_state`, `t` |-> `prepared:venom_state`] abi_encoder_prefix_eval) >>
     asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live c2.cs_next_var parent_ptr` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  mp_tac (Q.INST [`cursor_op` |-> `parent_ptr`, `value_op` |-> `next`, `st` |-> `c2`, `stored_st` |-> `c3`,
    `w` |-> `(old_word:bytes32)+size_word`, `s` |-> `prepared:venom_state`] abi_encoder_cursor_store_load) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `run_inst_seq (emitted_insts st final) initial = OK actual /\ inst_extends st final` by
    (mp_tac (Q.INST [`st1` |-> `c2`, `st2` |-> `final`, `s` |-> `initial:venom_state`,
      `s1` |-> `prepared:venom_state`, `s2` |-> `actual:venom_state`] abi_decode_sequence_chain) >>
     asm_simp_tac bool_ss []) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `abi_decode_frame slot 32 initial actual` by
    (irule abi_decode_frame_trans >> qexists_tac `prepared` >>
     asm_simp_tac bool_ss [abi_decode_frame_def]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >> rpt strip_tac >>
  `eval_operand op prepared = SOME w` by (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  qpat_x_assum `!op w. abi_decoder_operand_live c2.cs_next_var op /\ _ ==> _` irule >>
  asm_simp_tac bool_ss [] >> irule abi_decoder_operand_live_mono >>
  qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss [] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_FINISH_SEQUENCE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder parent finish not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayFinishSequence");

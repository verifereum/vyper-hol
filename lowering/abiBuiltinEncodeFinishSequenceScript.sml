(* Execute the actual builtin length store, preserving old operands and all
   memory outside the length word. Supports a method-ID prefix of any size. *)
Theory abiBuiltinEncodeFinishSequence
Ancestors
  abiBuiltinEncodeCode abiEncoderWrites abiBuiltinPrefix abiEncoderBytesPrefix
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderReentryAddress abiDecoderFrameCompose
  abiDecoderFrame abiDecoderArrayInitExec abiDecoderContract abiDecoderGuards abiDecoderArrayHeader
  emitHelperProps exprLoweringProps compileEnv emitHelper venomState venomExecSemantics venomMemProps
  words list arithmetic

Theorem abi_builtin_store_sequence:
  emit_void MSTORE [buf;value_op] st = ((),final) /\
  eval_operand buf s = SOME (n2w p) /\ eval_operand value_op s = SOME w /\
  p < dimword (:256) /\ fresh_vars_wrt limit_st s ==>
  run_inst_seq (emitted_insts st final) s = OK (mstore p w s) /\ inst_extends st final /\
  fresh_vars_wrt limit_st (mstore p w s) /\ mload p (mstore p w s) = w /\
  abi_decode_frame p 32 s (mstore p w s) /\
  (mstore p w s).vs_allocas = s.vs_allocas /\
  (mstore p w s).vs_alloca_next = s.vs_alloca_next /\
  (mstore p w s).vs_halted = s.vs_halted /\
  (!op. eval_operand op (mstore p w s) = eval_operand op s)
Proof
  strip_tac >> drule_all abi_encoder_emit_store >>
  simp[abi_decode_mstore_frame, mload_mstore_same, eval_operand_mstore]
QED

Theorem abi_builtin_encode_finish_sequence:
  abi_builtin_encode_finish buf encoded_len mid_size st = ((),final) /\
  eval_operand buf initial = SOME (n2w p) /\ eval_operand encoded_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var buf /\
  p < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\ inst_extends st final /\
    fresh_vars_wrt limit_st actual /\ mload p actual = n2w (len+mid_size) /\
    abi_decode_frame p 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  Cases_on `mid_size > 0`
  >- (asm_simp_tac bool_ss [abi_builtin_encode_finish_def, comp_bind_def, LET_THM] >>
      pairarg_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> gvs[] >>
      rename1 `emit_op ADD [encoded_len;Lit (n2w mid_size)] st = (total_op,prepared_st)` >>
      imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
      `prepared_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
      mp_tac (Q.INST [`lhs` |-> `encoded_len`, `rhs` |-> `Lit (n2w mid_size)`,
        `out` |-> `total_op`, `a` |-> `n2w len:bytes32`, `b` |-> `n2w mid_size:bytes32`,
        `st'` |-> `prepared_st`, `s` |-> `initial:venom_state`] abi_builtin_emit_add) >>
      impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
      rename1 `abi_builtin_prefix st prepared_st limit_st initial prepared` >>
      `eval_operand buf prepared = SOME (n2w p)` by
        (drule_all abi_encoder_prefix_eval >> simp[]) >>
      qpat_assum `abi_builtin_prefix _ _ _ _ _`
        (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
      mp_tac (Q.INST [`value_op` |-> `total_op`, `st` |-> `prepared_st`,
        `s` |-> `prepared:venom_state`, `w` |-> `n2w (len+mid_size):bytes32`] abi_builtin_store_sequence) >>
      impl_tac >- asm_simp_tac (srw_ss()) [word_add_n2w] >> strip_tac >>
      `run_inst_seq (emitted_insts st final) initial = OK (mstore p (n2w (len+mid_size)) prepared) /\
       inst_extends st final` by
        (mp_tac (Q.INST [`st1` |-> `prepared_st`, `st2` |-> `final`,
          `s` |-> `initial:venom_state`, `s1` |-> `prepared:venom_state`,
          `s2` |-> `mstore p (n2w (len+mid_size)) prepared`] abi_decode_sequence_chain) >>
         asm_simp_tac bool_ss []) >>
      qpat_assum `abi_decoder_address_frame _ _ _`
        (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
      `abi_decode_frame p 32 initial (mstore p (n2w (len+mid_size)) prepared)` by
        (irule abi_decode_frame_trans >> qexists_tac `prepared` >>
         asm_simp_tac bool_ss [abi_decode_frame_def]) >>
      qexists_tac `mstore p (n2w (len+mid_size)) prepared` >> asm_simp_tac bool_ss [] >>
      rpt strip_tac >> first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `mid_size = 0` by decide_tac >> gvs[abi_builtin_encode_finish_def] >> strip_tac >>
  drule_all abi_builtin_store_sequence >> strip_tac >>
  qexists_tac `mstore p (n2w len) initial` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_FINISH_SEQUENCE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin encoder finish sequence not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeFinishSequence");

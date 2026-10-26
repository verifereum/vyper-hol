(* Execute the actual scalar exits, including the dynamic branch's discarded load. *)
Theory abiEncoderArrayExitSequence
Ancestors
  abiEncoderSequenceReach abiEncoderArrayScalarCode abiEncoderArrayCode
  abiEncoderBytesPrefix abiBuiltinPrefix abiDecoderDynamicLoopSetup abiDecoderReentryAddress abiDecoderReentry
  abiDecoderContract compileEnv emitHelperProps exprLoweringProps
  venomExecSemantics venomState venomInst words list arithmetic

Theorem abi_encode_array_static_exit_sequence:
  abi_encode_array_static_exit src asz st = (out,final) /\
  eval_operand src initial = SOME (n2w sb) /\ mload sb initial = n2w cnt /\
  sb < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial ==>
  ?actual. eval_operand out actual = SOME (n2w (32+cnt*asz)) /\
    abi_builtin_prefix st final limit_st initial actual
Proof
  simp_tac bool_ss [abi_encode_array_static_exit_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op MLOAD [src] st = (len,c1)` >>
  rename1 `emit_op MUL [len;Lit (n2w asz)] c1 = (payload,c2)` >>
  rename1 `emit_op ADD [Lit 32w;payload] c2 = (out,ready)` >>
  imp_res_tac emitted_insts_emit_op >>
  `c1.cs_next_var <= limit_st.cs_next_var /\ c2.cs_next_var <= limit_st.cs_next_var /\
   st.cs_next_var <= c1.cs_next_var /\ st.cs_next_var <= c2.cs_next_var` by decide_tac >>
  drule_all abi_builtin_emit_load >> strip_tac >>
  rename1 `abi_builtin_prefix st c1 limit_st initial loaded` >>
  `eval_operand len loaded = SOME (n2w cnt) /\ fresh_vars_wrt limit_st loaded` by
    fs[abi_builtin_prefix_def, w2n_n2w] >>
  mp_tac (Q.INST [`lhs` |-> `len`, `rhs` |-> `Lit (n2w asz)`, `out` |-> `payload`,
    `a` |-> `n2w cnt:bytes32`, `b` |-> `n2w asz:bytes32`,
    `st` |-> `c1`, `st'` |-> `c2`, `s` |-> `loaded:venom_state`] abi_builtin_emit_mul) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `abi_builtin_prefix c1 c2 limit_st loaded prepared` >>
  `abi_builtin_prefix st c2 limit_st initial prepared` by
    (irule abi_builtin_prefix_chain >> qexistsl_tac [`c1`, `loaded`] >> asm_simp_tac bool_ss []) >>
  `fresh_vars_wrt limit_st prepared` by fs[abi_builtin_prefix_def] >>
  mp_tac (Q.INST [`lhs` |-> `Lit 32w`, `rhs` |-> `payload`,
    `a` |-> `32w:bytes32`, `b` |-> `(n2w cnt:bytes32)*n2w asz`,
    `st` |-> `c2`, `st'` |-> `ready`, `s` |-> `prepared:venom_state`] abi_builtin_emit_add) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `abi_builtin_prefix c2 ready limit_st prepared actual` >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss())
    [word_add_n2w, word_mul_n2w, AC ADD_COMM ADD_ASSOC, MULT_COMM] >>
  irule abi_builtin_prefix_chain >> qexistsl_tac [`c2`, `prepared`] >> asm_simp_tac bool_ss []
QED

Theorem abi_encode_array_dynamic_exit_sequence:
  abi_encode_array_dynamic_exit src dyn_ptr st = (out,final) /\
  eval_operand src initial = SOME src_word /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ mload slot initial = n2w offset /\
  slot < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial ==>
  ?actual. eval_operand out actual = SOME (n2w (32+offset)) /\
    abi_builtin_prefix st final limit_st initial actual
Proof
  simp_tac bool_ss [abi_encode_array_dynamic_exit_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op MLOAD [src] st = (ignored,c1)` >>
  rename1 `emit_op MLOAD [dyn_ptr] c1 = (off,c2)` >>
  rename1 `emit_op ADD [Lit 32w;off] c2 = (out,ready)` >>
  imp_res_tac emitted_insts_emit_op >>
  `c1.cs_next_var <= limit_st.cs_next_var /\ c2.cs_next_var <= limit_st.cs_next_var /\
   st.cs_next_var <= c1.cs_next_var /\ st.cs_next_var <= c2.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`src` |-> `src`, `p` |-> `src_word:bytes32`, `out` |-> `ignored`,
    `st` |-> `st`, `st'` |-> `c1`, `s` |-> `initial:venom_state`] abi_builtin_emit_load) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_builtin_prefix st c1 limit_st initial loaded` >>
  `eval_operand dyn_ptr loaded = SOME (n2w slot)` by
    (irule abi_encoder_prefix_eval >> qexistsl_tac [`limit_st`, `initial`, `st`, `c1`] >>
     asm_simp_tac bool_ss []) >>
  `mload slot loaded = n2w offset /\ fresh_vars_wrt limit_st loaded` by
    fs[abi_builtin_prefix_def, abi_decoder_address_frame_def, mload_def] >>
  mp_tac (Q.INST [`src` |-> `dyn_ptr`, `p` |-> `n2w slot:bytes32`, `out` |-> `off`,
    `st` |-> `c1`, `st'` |-> `c2`, `s` |-> `loaded:venom_state`] abi_builtin_emit_load) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_builtin_prefix c1 c2 limit_st loaded prepared` >>
  `eval_operand off prepared = SOME (n2w offset) /\ fresh_vars_wrt limit_st prepared` by
    fs[abi_builtin_prefix_def, w2n_n2w] >>
  `abi_builtin_prefix st c2 limit_st initial prepared` by
    (irule abi_builtin_prefix_chain >> qexistsl_tac [`c1`, `loaded`] >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`lhs` |-> `Lit 32w`, `rhs` |-> `off`,
    `a` |-> `32w:bytes32`, `b` |-> `n2w offset:bytes32`,
    `st` |-> `c2`, `st'` |-> `ready`, `s` |-> `prepared:venom_state`] abi_builtin_emit_add) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `abi_builtin_prefix c2 ready limit_st prepared actual` >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [word_add_n2w, ADD_COMM] >>
  irule abi_builtin_prefix_chain >> qexistsl_tac [`c2`, `prepared`] >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_EXIT_SEQUENCE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder array exit not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayExitSequence");

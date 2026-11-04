(* Execute the encoder's actual two-instruction contractABI$ceil32 computation on re-entry. *)
Theory abiEncoderRoundExecute
Ancestors
  abiEncoderBytesCode abiEncoderRounding abiBuiltinPrefix abiDecoderDynamicLoopSetup
  abiDecoderReentry abiDecoderContract emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomState venomInst words arithmetic list

Theorem abi_encode_round_sequence:
  abi_encode_round len st = (out,st') /\ eval_operand len s = SOME (n2w cnt) /\
  cnt+31 < dimword (:256) /\ st'.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s ==>
  ?t. eval_operand out t = SOME (n2w (contractABI$ceil32 cnt)) /\
    abi_builtin_prefix st st' limit_st s t
Proof
  simp_tac bool_ss [abi_encode_round_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [Lit 31w;len] st = (arg,c1)` >>
  rename1 `emit_op AND _ c1 = (out,end_st)` >>
  imp_res_tac emitted_insts_emit_op >>
  `c1.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= c1.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`lhs` |-> `Lit 31w`, `rhs` |-> `len`, `out` |-> `arg`, `st'` |-> `c1`,
    `a` |-> `31w:bytes32`, `b` |-> `n2w cnt:bytes32`] abi_builtin_emit_add) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `abi_builtin_prefix st c1 limit_st s prepared` >>
  `fresh_vars_wrt limit_st prepared` by fs[abi_builtin_prefix_def] >>
  mp_tac (Q.INST [`opc` |-> `AND`,
    `lhs` |-> `Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w`,
    `rhs` |-> `arg`, `out` |-> `out`, `st` |-> `c1`, `st'` |-> `end_st`,
    `s` |-> `prepared:venom_state`,
    `a` |-> `0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w:bytes32`,
    `b` |-> `31w+(n2w cnt:bytes32)`, `w` |-> `n2w (contractABI$ceil32 cnt):bytes32`]
    abi_builtin_emit_binary) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def, abi_encoder_round_ceil32] >> strip_tac >>
  rename1 `abi_builtin_prefix c1 end_st limit_st prepared actual` >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_builtin_prefix_chain >> qexistsl_tac [`c1`, `prepared`] >> asm_simp_tac bool_ss []
QED

Theorem abi_encode_round_live:
  abi_encode_round len st = (out,st') ==> abi_decoder_operand_live st'.cs_next_var out
Proof
  simp_tac bool_ss [abi_encode_round_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule abi_decoder_operand_live_emit >> simp[]
QED

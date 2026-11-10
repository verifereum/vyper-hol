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

Theorem abi_encode_ceil32_sequence:
  abi_encode_ceil32 len st = (out,st') /\ eval_operand len s = SOME (n2w cnt) /\
  abi_decoder_operand_live st.cs_next_var len /\
  cnt+31 < dimword (:256) /\ st'.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s ==>
  ?t. eval_operand out t = SOME (n2w (contractABI$ceil32 cnt)) /\
    abi_builtin_prefix st st' limit_st s t
Proof
  simp_tac bool_ss [abi_encode_ceil32_def, comp_bind_def, LET_THM] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op NOT [Lit 31w] st = (mask,c1)` >>
  rename1 `emit_op ADD [len;Lit 31w] c1 = (arg,c2)` >>
  imp_res_tac emitted_insts_emit_op >>
  `c1.cs_next_var <= limit_st.cs_next_var /\ c2.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`opc` |-> `NOT`, `ops` |-> `[Lit 31w]`, `out` |-> `mask`, `st'` |-> `c1`,
    `w` |-> `word_1comp (31w:bytes32)`] abi_builtin_emit_register) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> irule step_NOT >> simp[eval_operand_def]) >>
  strip_tac >> rename1 `abi_builtin_prefix st c1 limit_st s s1` >>
  `fresh_vars_wrt limit_st s1 /\ eval_operand len s1 = SOME (n2w cnt)` by
    (qpat_assum `abi_builtin_prefix st c1 _ _ _` mp_tac >>
     simp_tac bool_ss [abi_builtin_prefix_def, abi_decoder_address_frame_def] >>
     strip_tac >> asm_simp_tac bool_ss [] >> first_x_assum irule >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`lhs` |-> `len`, `rhs` |-> `Lit 31w`, `out` |-> `arg`, `st` |-> `c1`,
    `st'` |-> `c2`, `s` |-> `s1:venom_state`, `a` |-> `n2w cnt:bytes32`, `b` |-> `31w:bytes32`]
    abi_builtin_emit_add) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `abi_builtin_prefix c1 c2 limit_st s1 s2` >>
  `abi_decoder_operand_live c1.cs_next_var mask` by
    (qpat_assum `emit_op NOT _ _ = _` mp_tac >> simp_tac bool_ss [] >>
     disch_then (irule o MATCH_MP abi_decoder_operand_live_emit)) >>
  `fresh_vars_wrt limit_st s2 /\ eval_operand mask s2 = SOME (word_1comp 31w)` by
    (qpat_assum `abi_builtin_prefix c1 c2 _ _ _` mp_tac >>
     simp_tac bool_ss [abi_builtin_prefix_def, abi_decoder_address_frame_def] >>
     strip_tac >> asm_simp_tac bool_ss [] >> first_x_assum irule >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`opc` |-> `AND`, `lhs` |-> `arg`, `rhs` |-> `mask`, `st` |-> `c2`,
    `st'` |-> `st'`, `s` |-> `s2:venom_state`, `a` |-> `n2w cnt + 31w:bytes32`,
    `b` |-> `word_1comp (31w:bytes32)`, `w` |-> `n2w (contractABI$ceil32 cnt):bytes32`]
    abi_builtin_emit_binary) >>
  impl_tac
  >- (`(n2w cnt + 31w:bytes32) && word_1comp 31w = n2w (contractABI$ceil32 cnt)` by
        (`word_1comp (31w:bytes32) =
          0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w` by blastLib.BBLAST_TAC >>
         asm_rewrite_tac [] >> ONCE_REWRITE_TAC [WORD_AND_COMM] >>
         ONCE_REWRITE_TAC [WORD_ADD_COMM] >> irule abi_encoder_round_ceil32 >>
         asm_simp_tac (srw_ss()) []) >>
      asm_simp_tac bool_ss []) >>
  strip_tac >> rename1 `abi_builtin_prefix c2 st' limit_st s2 actual` >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_builtin_prefix_chain >> qexistsl_tac [`c2`, `s2`] >> asm_simp_tac arith_ss [] >>
  irule abi_builtin_prefix_chain >> qexistsl_tac [`c1`, `s1`] >> asm_simp_tac arith_ss []
QED

Theorem abi_encode_round_live:
  abi_encode_round len st = (out,st') ==> abi_decoder_operand_live st'.cs_next_var out
Proof
  simp_tac bool_ss [abi_encode_round_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule abi_decoder_operand_live_emit >> simp[]
QED

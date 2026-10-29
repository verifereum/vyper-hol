(* The optional head-window check before decoding tuple or struct members. *)
Theory abiDecoderComplexHead
Ancestors
  abiDecoderBytesBound abiDecoderGuard abiDecoderGuards abiDecoderReservation abiDecoderContract
  compileEnv emitHelper emitHelperProps exprLoweringProps venomExecSemantics venomState
  venomInst words arithmetic rich_list

Definition abi_decode_complex_head_guard_def:
  abi_decode_complex_head_guard src hi head_sz =
    if hi = Lit 0w then return ()
    else do end_op <- emit_op ADD [src; Lit (n2w head_sz)];
            abi_decode_le_guard end_op hi
         od
End

Theorem abi_decode_complex_head_guard_sequence:
  abi_decode_complex_head_guard src hi head_sz st = ((),st') /\
  eval_operand src s = SOME (n2w sb) /\
  (hi = Lit 0w \/ ?hb. eval_operand hi s = SOME (n2w hb) /\
                      sb + head_sz <= hb /\ hb < dimword (:256)) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  Cases_on `hi = Lit 0w`
  >- (simp[abi_decode_complex_head_guard_def, comp_return_def] >> strip_tac >>
      gvs[] >> qexists_tac `s` >> simp[emitted_insts_def, run_inst_seq_def,
        inst_extends_refl]) >>
  simp[abi_decode_complex_head_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [src; Lit (n2w head_sz)] st = (end_op,c1)` >>
  rename1 `eval_operand hi s = SOME (n2w hb)` >>
  `eval_operand (Lit (n2w head_sz)) s = SOME (n2w head_sz)` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand hi s1 = SOME (n2w hb)` by metis_tac[] >>
  `sb + head_sz < dimword (:256)` by decide_tac >>
  `w2n ((n2w sb : bytes32) + n2w head_sz) <= w2n (n2w hb : bytes32)` by
    simp[word_add_n2w, w2n_n2w] >>
  drule_all abi_decode_le_guard_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  drule abi_decode_le_guard_shape >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `t` >> gvs[] >> metis_tac[]
QED

Theorem abi_decode_complex_head_guard_shape:
  abi_decode_complex_head_guard src hi head_sz st = ((),st') ==>
  st.cs_next_id <= st'.cs_next_id /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')
Proof
  Cases_on `hi = Lit 0w` >>
  simp[abi_decode_complex_head_guard_def, abi_decode_le_guard_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, is_terminator_def, is_alloca_op_def, mk_inst_def]
QED

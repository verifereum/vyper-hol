(* Successful unsigned ABI clamps preserve the decoded word and source state. *)
Theory abiDecoderUnsignedClamp
Ancestors
  abiDecoderGuards abiDecoderContract abiEncoder emitHelperProps exprLoweringProps
  compileEnv emitHelper valueEncoding venomExecSemantics venomState venomInst
  words arithmetic rich_list list

Theorem abi_unsigned_clamp_dimindex[simp,local]: dimindex (:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

Theorem abi_decoder_unsigned_shift_zero:
  bits <= 256 /\ w2n (w:bytes32) < 2 ** bits ==>
  w >>> w2n (n2w bits : bytes32) = 0w
Proof
  strip_tac >>
  `bits < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
  asm_simp_tac bool_ss [w2n_n2w, LESS_MOD] >>
  ONCE_REWRITE_TAC [GSYM w2n_eq_0] >>
  asm_simp_tac bool_ss [w2n_lsr, LESS_DIV_EQ_ZERO]
QED

Theorem abi_decoder_clamp_emit_frame:
  emit_op opc ops st = (v,st') /\
  (opc = EQ \/ opc = SIGNEXTEND \/ opc = SHL \/ opc = SHR \/ opc = ISZERO) /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_data_section = s.vs_data_section
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def] >>
  gvs[Once step_inst_base_def, mk_inst_def] >>
  gvs[exec_pure2_def, exec_pure1_def, AllCaseEqs(), update_var_def]
QED

Theorem abi_decoder_unsigned_clamp_sequence:
  compile_abi_int_clamp val_op bits F st = ((),st') /\
  eval_operand val_op s = SOME w /\ bits <= 256 /\
  w2n w < 2 ** bits /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    fresh_vars_wrt st' t /\
    (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  simp_tac bool_ss [compile_abi_int_clamp_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >> pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op SHR [Lit (n2w bits); val_op] st = (shifted,c1)` >>
  rename1 `emit_op ISZERO [shifted] c1 = (ok,c2)` >>
  `eval_operand (Lit (n2w bits)) s = SOME (n2w bits)` by simp[eval_operand_def] >>
  drule_all abi_decoder_unsigned_shift_zero >> strip_tac >>
  drule_all emit_op_SHR_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  gvs[] >> drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  gvs[bool_to_word_def] >>
  `(1w:bytes32) <> 0w` by simp[] >>
  drule_all emit_void_ASSERT_ok_full >> simp[] >> strip_tac >> gvs[] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `SHR`] abi_decoder_clamp_emit_frame)) >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ISZERO`] abi_decoder_clamp_emit_frame)) >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `run_inst_seq (emitted_insts st c2) s = OK s2 /\ inst_extends st c2` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `c1`] >> simp[]) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `s2` >> simp[] >> metis_tac[]
QED

Theorem abi_decoder_unsigned_clamp_shape:
  compile_abi_int_clamp val_op bits F st = ((),st') ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             ~is_alloca_op i.inst_opcode) (emitted_insts st st')
Proof
  simp[compile_abi_int_clamp_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       emitted_insts_def, IS_PREFIX_APPEND] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, is_terminator_def, is_alloca_op_def, mk_inst_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_UNSIGNED_CLAMP_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI unsigned clamp not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderUnsignedClamp");

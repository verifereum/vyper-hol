(* The computed head length uses the existing cursor observation contract at that value. *)
Theory abiEncoderArrayTailInitSequence
Ancestors
  abiEncoderArrayTailInitCode abiEncoderComplexPrefixReach abiEncoderComplexPrefix
  abiDecoderIndexInit abiDecoderReentryAllocation abiDecoderReentryAddress abiDecoderArrayInitExec
  abiDecoderAllocation abiDecoderReentry abiDecoderArrayHeader abiDecoderGuards abiDecoderContract
  abiDecoderFrame emitHelperProps exprLoweringProps compileEnv emitHelper context
  venomExecSemantics venomMemProps venomState venomInst finite_map words list arithmetic

Theorem abi_encode_array_tail_init_sequence:
  abi_encode_array_tail_init count_op asz st = (dyn_ptr,st') /\
  eval_operand count_op initial = SOME (n2w cnt) /\ abi_decoder_operand_live st.cs_next_var count_op /\
  abi_decoder_budget first last b cap initial /\ st.cs_next_id IN abi_decoder_ids first last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    abi_encoder_complex_prefix_post [(AbiPrimWord,cnt*asz,0,F)] dyn_ptr st.cs_next_var st.cs_next_id
      limit_st first last b cap initial actual
Proof
  strip_tac >> drule abi_encode_array_tail_init_trace >> strip_tac >>
  drule abi_encode_array_tail_init_shape >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  `c1.cs_next_var <= limit_st.cs_next_var /\ c2.cs_next_var <= limit_st.cs_next_var /\
   st.cs_next_var <= c1.cs_next_var` by decide_tac >>
  drule_all abi_decoder_alloc_buffer_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) initial = OK allocated` >>
  `eval_operand count_op allocated = SOME (n2w cnt)` by asm_simp_tac bool_ss [] >>
  mp_tac (Q.INST [`opc` |-> `MUL`, `lhs` |-> `count_op`, `rhs` |-> `Lit (n2w asz)`,
    `out` |-> `offset`, `a` |-> `n2w cnt:bytes32`, `b` |-> `n2w asz:bytes32`,
    `st` |-> `c1`, `st'` |-> `c2`, `s` |-> `allocated:venom_state`] abi_decoder_binary_reentry) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) allocated = OK prepared` >>
  `abi_decoder_operand_live c1.cs_next_var dyn_ptr` by
    (asm_simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     rpt strip_tac >> decide_tac) >>
  `eval_operand buf.buf_operand prepared = SOME (n2w p)` by
    (qpat_assum `!op. abi_decoder_operand_live c1.cs_next_var op ==> _`
      (qspec_then `dyn_ptr` mp_tac) >> gvs[]) >>
  `eval_operand offset prepared = SOME (n2w (cnt*asz))` by
    fs[word_mul_n2w, MULT_COMM, eval_operand_def, lookup_var_update_var] >>
  drule abi_decoder_budget_word_bound >> strip_tac >> `p < dimword (:256)` by decide_tac >>
  `run_inst_seq (emitted_insts c2 st') prepared = OK (mstore p (n2w (cnt*asz)) prepared)` by
    (drule_all abi_decode_store_sequence >> asm_simp_tac (srw_ss()) [w2n_n2w]) >>
  `inst_extends st c1 /\ inst_extends c2 st'` by
    (conj_tac >- (drule abi_decode_alloc_buffer_inst_extends >> simp[]) >>
     drule inst_extends_emit_void >> simp[]) >>
  `run_inst_seq (emitted_insts st c2) initial = OK prepared /\ inst_extends st c2` by
    (drule_all abi_decode_sequence_chain >> asm_simp_tac bool_ss []) >>
  `run_inst_seq (emitted_insts st st') initial = OK (mstore p (n2w (cnt*asz)) prepared)` by
    (drule_all abi_decode_sequence_chain >> asm_simp_tac bool_ss []) >>
  `abi_decoder_budget first last b cap prepared` by
    (drule_all abi_decoder_budget_transport >> asm_simp_tac bool_ss []) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op prepared = eval_operand op initial` by
    (rpt strip_tac >> `abi_decoder_operand_live c1.cs_next_var op` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []) >>
     asm_simp_tac bool_ss []) >>
  `abi_decode_frame p 32 prepared (mstore p (n2w (cnt*asz)) prepared)` by irule abi_decode_mstore_frame >>
  qexists_tac `mstore p (n2w (cnt*asz)) prepared` >> asm_simp_tac bool_ss [] >>
  pure_rewrite_tac [abi_encoder_complex_prefix_post_def] >> qexists_tac `p` >>
  gvs[fresh_vars_wrt_mstore, eval_operand_mstore, abi_decode_frame_def, mload_mstore_same,
    mstore_def, write_memory_with_expansion_def] >> first_assum ACCEPT_TAC
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_TAIL_INIT_SEQUENCE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder tail initialization execution not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayTailInitSequence");

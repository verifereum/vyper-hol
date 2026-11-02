(* Actual word/copy encoder execution, reusing snapshot-copy and word proofs.
   These leaves do not allocate. MCOPY itself permits overlapping intervals. *)
Theory abiEncoderLeaves
Ancestors
  abiDecoderWordCopy abiDecoderComposition abiDecoderContract abiDecoderCopy
  abiEncoder emitHelperProps exprLoweringProps emitHelper compileEnv valueEncoding
  venomState venomExecSemantics venomInst words list

Theorem abi_encode_word_decode_code:
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,st') ==>
  out = Lit 32w /\
  compile_abi_decode_to_buf dst src MLOAD (Lit 0w) (DecPrimWord NoClamp) st = ((),st')
Proof
  simp[Once compile_abi_encode_child_def, compile_abi_encode_static_def,
       compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
       compile_abi_clamp_basetype_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem abi_encode_word_sequence:
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,st') /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  sb < dimword (:256) /\ d < dimword (:256) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand out t = SOME 32w /\
    mem_bytes_at d 32 t.vs_memory = mem_bytes_at sb 32 s.vs_memory /\
    abi_decode_frame d 32 s t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >> drule abi_encode_word_decode_code >> strip_tac >>
  mp_tac (Q.INST [`opc` |-> `MLOAD`, `hi` |-> `Lit 0w`] abi_decode_word_copied_window) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_decode_source_opcode_def] >>
  gvs[abi_decode_source_def, eval_operand_def]
QED

Theorem abi_encode_copy_code:
  compile_abi_encode_to_buf dst src (AbiCopy sz) st = (out,st') ==>
  out = Lit (n2w sz) /\ emit_void MCOPY [dst;src;Lit (n2w sz)] st = ((),st')
Proof
  simp[Once compile_abi_encode_child_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[]
QED

Theorem abi_encode_copy_sequence:
  compile_abi_encode_to_buf dst src (AbiCopy sz) st = (out,st') /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w db) /\
  sb < dimword (:256) /\ db < dimword (:256) /\ sz < dimword (:256) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand out t = SOME (n2w sz) /\
    mem_bytes_at db sz t.vs_memory = mem_bytes_at sb sz s.vs_memory /\
    abi_decode_frame db sz s t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >> drule abi_encode_copy_code >> strip_tac >>
  `emit_void (abi_decode_copy_opcode MLOAD) [dst;src;Lit (n2w sz)] st = ((),st')` by
    simp[abi_decode_copy_opcode_def] >>
  mp_tac (Q.INST [`opc` |-> `MLOAD`, `sz_op` |-> `Lit (n2w sz)`,
    `p` |-> `n2w sb:bytes32`, `d` |-> `n2w db:bytes32`, `n` |-> `n2w sz:bytes32`]
    abi_decode_copy_sequence) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_decode_source_opcode_def, eval_operand_def] >>
  strip_tac >> rename1 `run_inst_seq (emitted_insts st st') s = OK actual` >>
  `fresh_vars_wrt st' actual` by
    (irule abi_decode_copy_fresh >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`dst`, `MLOAD`, `s`, `src`, `st`, `Lit (n2w sz)`] >>
     asm_simp_tac (srw_ss()) [abi_decode_source_opcode_def]) >>
  qexists_tac `actual` >>
  gvs[abi_decode_copy_bytes_def, abi_decode_source_def, mem_bytes_at_def, w2n_n2w,
      eval_operand_def]
QED

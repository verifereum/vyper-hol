(* An unclamped word decode preserves its exact canonical 32-byte window. *)
Theory abiDecoderWordCopy
Ancestors
  abiDecoderContract abiCanonicalLoad valueEncoding valueEncodingProps
  venomState venomExecSemantics integer_word words

Theorem abi_decode_load_mload:
  sb < dimword (:256) ==>
  abi_decode_load opc (n2w sb : bytes32) s =
    mload sb (s with vs_memory := abi_decode_source opc s)
Proof
  strip_tac >> Cases_on `opc = MLOAD` >>
  simp[abi_decode_load_def, abi_decode_source_def, mload_def, w2n_n2w]
QED

Theorem abi_decode_word_copied_window:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord NoClamp) st = ((),st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\ sb < dimword (:256) /\ d < dimword (:256) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_bytes_at d 32 t.vs_memory = mem_bytes_at sb 32 (abi_decode_source opc s) /\
    abi_decode_frame d 32 s t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >> drule_all abi_decode_word_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK t` >>
  `mem_word_at d t.vs_memory = abi_decode_load opc (n2w sb : bytes32) s` by
    gvs[val_in_memory_def, val_to_w256_def, i2w_pos, n2w_w2n] >>
  `mload d t = mload sb (s with vs_memory := abi_decode_source opc s)` by
    (irule EQ_TRANS >> qexists_tac `abi_decode_load opc (n2w sb : bytes32) s` >>
     conj_tac >- asm_rewrite_tac[GSYM mem_word_at_eq_mload] >>
     irule abi_decode_load_mload >> first_assum ACCEPT_TAC) >>
  `mem_bytes_at d 32 t.vs_memory = mem_bytes_at sb 32 (abi_decode_source opc s)` by
    (drule_all mload_eq_mem_bytes_at_eq >> simp[]) >>
  qexists_tac `t` >> simp[]
QED

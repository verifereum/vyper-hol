(* Probe: dynamic bytes retain an exact safe trace before CPS conversion. *)
Theory decoderPrefixSafety
Ancestors
  calldataBytesLive calldataBytesLeaf fragExecMem list

Theorem calldata_bytes_safe_exact_run:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (DecBytestring maxn) st = ((),st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  d + abi_decode_bytes_copy_size maxn < dimword (:256) /\
  d + abi_decode_bytes_copy_size maxn <= s.vs_alloca_next /\
  maxn < dimword (:256) /\
  w2n (abi_decode_load CALLDATALOAD p s) <= maxn ==>
  (?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p s /\
    mem_bytes_at d (abi_decode_bytes_copy_size maxn) t.vs_memory =
      mem_bytes_at (w2n p) (abi_decode_bytes_copy_size maxn) s.vs_call_ctx.cc_calldata /\
    abi_decode_frame d (abi_decode_bytes_copy_size maxn) s t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next) /\
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >> conj_tac
  >- (drule_all calldata_bytes_accepted_live >> simp[]) >>
  irule run_inst_seq_mem_ok_of_prefix_safe >> reverse conj_tac
  >- (drule calldata_bytes_opcodes >> simp[EVERY_MEM] >> metis_tac[]) >>
  drule_at (Pos hd) calldata_bytes_prefix_live >> simp[] >> metis_tac[]
QED

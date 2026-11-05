(* Canonical calldata bytes decoding without a scratch arena premise. *)
Theory entryReachBodyCanonicalBytes
Ancestors
  calldataBytesLive abiDecoderBytesTyped abiCanonicalBytes
  abiDecoderContract abiDecoderFrame valueEncoding valueEncodingProps
  vyperValue vyperTyping contractABI words arithmetic

Theorem entry_canonical_bytes_sequence:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (DecBytestring n) st = ((),st') /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  LENGTH bs <= n /\ n < dimword (:256) /\
  sb + LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)) < dimword (:256) /\
  d + abi_decode_bytes_copy_size n < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)))
    s.vs_call_ctx.cc_calldata = enc (Bytes NONE) (contractABI$BytesV bs) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) d t.vs_memory /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) s t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `sb < dimword (:256) /\ LENGTH bs < dimword (:256)` by decide_tac >>
  `abi_decode_load CALLDATALOAD (n2w sb : bytes32) s = n2w (LENGTH bs)` by
    (irule canonical_bytes_count_load >> asm_simp_tac bool_ss [abi_decode_source_def]) >>
  `w2n (abi_decode_load CALLDATALOAD (n2w sb : bytes32) s) <= n` by simp[] >>
  drule_all calldata_bytes_accepted_live >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK t` >>
  `val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) d t.vs_memory` by
    (irule canonical_bytes_copied_layout >>
     reverse conj_tac
     >- (simp[val_wf_def, GSYM (cj 2 abi_decoder_bytes_copy_size)] >>
         mp_tac (cj 3 abi_decoder_bytes_copy_size) >> decide_tac) >>
     qexistsl_tac [`abi_decode_bytes_copy_size n`, `sb`, `s.vs_call_ctx.cc_calldata`] >>
     simp[val_wf_def, GSYM (cj 2 abi_decoder_bytes_copy_size)]) >>
  qexists_tac `t` >> simp[]
QED

(* Complete emitted bytes/string encoder execution under enclosing freshness. *)
Theory abiEncoderBytesCorrect
Ancestors
  abiEncoderBytesBody abiEncoderBytesContract abiEncoderBytesPrefix abiEncoderBytesCode
  abiEncoderInput abiEncoderMemory abiEncoderRounding abiBuiltinPrefix abiDecoderDynamicLoopSetup
  abiDecoderReentry abiDecoderGuards abiDecoderContract valueEncoding valueEncodingProps
  compileEnv emitHelper venomState venomExecSemantics words list arithmetic

Theorem abi_encoder_bytes_sequence:
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) st = (out,final) /\
  abi_encoder_input (AbiBytestring maxlen) at av sb cap s.vs_memory /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w db) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  sb < dimword (:256) /\ db+LENGTH (enc at av) < dimword (:256) /\
  (sb+cap <= db \/ db+LENGTH (enc at av) <= sb) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. run_inst_seq (emitted_insts st final) s = OK actual /\ inst_extends st final /\
    mem_bytes_at db (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\ fresh_vars_wrt limit_st actual /\
    abi_decode_frame db (LENGTH (enc at av)) s actual /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_input _ _ _ _ _ _`
    (qx_choose_then `bs` (MAP_EVERY assume_tac o CONJUNCTS) o REWRITE_RULE [abi_encoder_input_bytes_iff]) >>
  qpat_x_assum `av = contractABI$BytesV bs` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`bs` |-> `bs:byte list`] abi_encoder_bytes_encoding) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`cnt` |-> `LENGTH (bs:byte list)`] abi_encoder_ceil32_bounds) >> strip_tac >>
  drule abi_encode_bytes_trace >> strip_tac >> drule abi_encode_bytes_suffix_shape >> strip_tac >>
  drule abi_encode_bytes_copy_shape >> strip_tac >> drule abi_encode_bytes_prefix_shape >> strip_tac >>
  `copied.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= copied.cs_next_var /\
   LENGTH bs+31 < dimword (:256) /\ db+contractABI$ceil32 (LENGTH bs) < dimword (:256) /\
   32+LENGTH bs < dimword (:256)` by decide_tac >>
  `mload sb s = n2w (LENGTH bs)` by fs[mem_word_at_eq_mload] >>
  mp_tac (Q.INST [`cnt` |-> `LENGTH (bs:byte list)`] abi_encode_bytes_body_sequence) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st copied) s = OK prepared` >>
  mp_tac (Q.INST [`len` |-> `FST (ops:operand # operand)`, `cnt` |-> `LENGTH (bs:byte list)`,
    `st` |-> `copied`, `st'` |-> `final`, `s` |-> `prepared:venom_state`]
    abi_encode_bytes_suffix_sequence) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_builtin_prefix copied final limit_st prepared actual` >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  `sb+(32+LENGTH bs) <= db \/ db+(32+contractABI$ceil32 (LENGTH bs)) <= sb` by decide_tac >>
  `mem_bytes_at db (LENGTH (enc at (contractABI$BytesV bs)))
    (mcopy db sb (32+LENGTH bs) (mstore (db+contractABI$ceil32 (LENGTH bs)) 0w s)).vs_memory =
    enc at (contractABI$BytesV bs)` by
    (mp_tac (Q.INST [`maxlen` |-> `maxlen`, `cap` |-> `cap`] abi_encoder_bytes_input_memory) >>
     asm_simp_tac bool_ss []) >>
  `abi_decode_frame db (32+contractABI$ceil32 (LENGTH bs)) s
    (mcopy db sb (32+LENGTH bs) (mstore (db+contractABI$ceil32 (LENGTH bs)) 0w s))` by
    (irule abi_encoder_bytes_write_frame >> asm_simp_tac bool_ss []) >>
  `abi_decode_frame db (32+contractABI$ceil32 (LENGTH bs)) s actual` by
    (mp_tac (Q.INST [`t` |-> `mcopy db sb (32+LENGTH (bs:byte list))
        (mstore (db+contractABI$ceil32 (LENGTH (bs:byte list))) 0w s)`,
      `u` |-> `actual:venom_state`, `sz` |-> `32+contractABI$ceil32 (LENGTH (bs:byte list))`]
      abi_encoder_frame_memory) >> asm_simp_tac bool_ss []) >>
  `!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
    eval_operand op actual = SOME w` by
    (rpt strip_tac >> `abi_decoder_operand_live copied.cs_next_var op` by
      (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []) >>
     `eval_operand op prepared = SOME w` by (first_x_assum irule >> asm_simp_tac bool_ss []) >>
     first_x_assum irule >> asm_simp_tac bool_ss []) >>
  (qexists_tac `actual` >> asm_simp_tac (srw_ss()) [abi_encoder_bytes_padded_length] >>
   qpat_x_assum `mem_bytes_at db (LENGTH (enc at _)) _ = _` mp_tac >>
   asm_simp_tac (srw_ss()) [abi_encoder_bytes_padded_length])
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_BYTES_CORRECT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder bytes correctness not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderBytesCorrect");

(* Execute the bytes encoder through its copy, preserving the loaded length. *)
Theory abiEncoderBytesBody
Ancestors
  abiEncoderBytesCode abiEncoderBytesPrefix abiEncoderBytesCopy abiEncoderMemory
  abiBuiltinPrefix abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderGuards
  abiDecoderContract compileEnv emitHelper valueEncoding venomState venomExecSemantics
  words arithmetic list

Theorem abi_encode_bytes_body_sequence:
  abi_encode_bytes_prefix dst src st = (ops,ready) /\
  abi_encode_bytes_copy dst src (FST ops) (SND ops) ready = ((),copied) /\
  eval_operand src s = SOME (n2w sb) /\ mload sb s = n2w cnt /\ eval_operand dst s = SOME (n2w db) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  sb < dimword (:256) /\ cnt+31 < dimword (:256) /\
  db+contractABI$ceil32 cnt < dimword (:256) /\ 32+cnt < dimword (:256) /\
  copied.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. run_inst_seq (emitted_insts st copied) s = OK actual /\ inst_extends st copied /\
    fresh_vars_wrt limit_st actual /\ eval_operand (FST ops) actual = SOME (n2w cnt) /\
    abi_decoder_operand_live copied.cs_next_var (FST ops) /\
    actual.vs_memory = (mcopy db sb (32+cnt) (mstore (db+contractABI$ceil32 cnt) 0w s)).vs_memory /\
    actual.vs_call_ctx = s.vs_call_ctx /\ actual.vs_data_section = s.vs_data_section /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encode_bytes_prefix_shape >> strip_tac >> drule abi_encode_bytes_copy_shape >> strip_tac >>
  `ready.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= ready.cs_next_var /\
   ready.cs_next_var <= copied.cs_next_var` by decide_tac >>
  drule_all abi_encode_bytes_prefix_sequence >> strip_tac >>
  rename1 `abi_builtin_prefix st ready limit_st s prepared` >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `eval_operand src prepared = SOME (n2w sb) /\ eval_operand dst prepared = SOME (n2w db)` by
    (conj_tac >> first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live ready.cs_next_var src /\ abi_decoder_operand_live ready.cs_next_var dst` by
    (conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`len` |-> `FST (ops:operand # operand)`, `lastptr` |-> `SND (ops:operand # operand)`,
    `st` |-> `ready`, `st'` |-> `copied`, `s` |-> `prepared:venom_state`,
    `rounded` |-> `contractABI$ceil32 cnt`] abi_encode_bytes_copy_sequence) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts ready copied) prepared = OK actual` >>
  `eval_operand (FST ops) actual = SOME (n2w cnt)` by
    (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live copied.cs_next_var (FST ops)` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `ready.cs_next_var` >> asm_simp_tac bool_ss []) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  `actual.vs_memory = (mcopy db sb (32+cnt) (mstore (db+contractABI$ceil32 cnt) 0w s)).vs_memory` by
    (irule EQ_TRANS >>
     qexists_tac `(mcopy db sb (32+cnt) (mstore (db+contractABI$ceil32 cnt) 0w prepared)).vs_memory` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule abi_encoder_bytes_write_memory_cong >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >> rpt strip_tac >>
  `abi_decoder_operand_live ready.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []) >>
  `eval_operand op prepared = SOME w` by (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  first_x_assum irule >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_BYTES_BODY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder bytes body not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderBytesBody");

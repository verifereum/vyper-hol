(* Reuse the checked tuple word slot to execute an Empty initializer store. *)
Theory abiEmptyWord
Ancestors
  abiTupleEncodeSlot abiTupleEncodeInput abiTupleProps abiEncoderInput
  abiEncoderMemory abiDecoderReentry abiDecoderContract exprLowering
  emitHelperProps exprLoweringProps compileEnv context venomState
  venomExecSemantics finite_map words list arithmetic contractABI
Libs
  wordsLib

Theorem abi_empty_zero_word_input:
  abi_tuple_encode_input sf ce (BaseT (UintT 256)) (Uint 256) (NumV 0)
    (Lit 0w) next lo hi s
Proof
  simp[abi_tuple_encode_input_def, abi_decoder_operand_live_def,
    is_word_type_def, type_memory_bytes_def, eval_operand_def,
    has_type_def, valid_int_bound_def, is_dynamic_def, static_length_def, enc_def, enc_number_def,
    dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Theorem abi_empty_word_slot:
  compile_abi_tuple_slot (ARB:compile_env) base_op off (Lit 0w)
    (BaseT (UintT 256)) st = ((),final) /\
  eval_operand base_op s = SOME (n2w p) /\ p+off < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. run_inst_seq (emitted_insts st final) s = OK actual /\ inst_extends st final /\
    mem_bytes_at (p+off) 32 actual.vs_memory = REPLICATE 32 0w /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame (p+off) 32 s actual /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`ce` |-> `ARB:compile_env`,
    `buf` |-> `base_op:operand`, `baddr` |-> `p:num`, `lo` |-> `0:num`, `hi` |-> `0:num`,
    `ty` |-> `BaseT (UintT 256)`, `at` |-> `Uint 256`,
    `av` |-> `NumV 0`, `op` |-> `Lit 0w`] abi_tuple_encode_slot_sequence) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_empty_zero_word_input] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) s = OK actual` >>
  `mem_bytes_at (p+off) 32 actual.vs_memory = REPLICATE 32 0w` by
    (qpat_x_assum `abi_encoder_input _ _ _ _ _ _` mp_tac >>
     simp[type_to_abi_enc_info_def, type_memory_bytes_def,
       abi_encoder_input_copy_iff, enc_def, enc_number_def, abi_encoder_zero_word]) >>
  qpat_x_assum `abi_decode_frame _ _ _ _`
    (assume_tac o SIMP_RULE (srw_ss()) [type_memory_bytes_def]) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [type_memory_bytes_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_EMPTY_WORD_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI empty word not kernel closed: " ^ n)
  end) (DB.thms "abiEmptyWord");


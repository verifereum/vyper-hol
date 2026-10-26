(* Execute the complete Empty producer from actual allocation through zero stores.
   Reused allocations may contain arbitrary stale memory before initialization. *)
Theory abiEmptyAllocate
Ancestors
  abiEmptyAllocateCode abiEmptyAllocateEffect abiEmptySequence abiEmptyEffect
  abiBuiltinAllocationState abiBuiltinEncodeFinishSequence abiEncoderMemory
  abiDecoderGuards abiDecoderReentry abiDecoderContract abiEmptyCode
  exprLoweringProps compileEnv builtinSimple emitHelper venomState
  venomExecSemantics words list arithmetic

Definition abi_empty_initialized_bytes_def:
  abi_empty_initialized_bytes outsz length_only =
    if length_only then 32 else 32*((outsz+31) DIV 32)
End

Theorem abi_empty_initializer_execute:
  (if length_only then emit_void MSTORE [base_op;Lit 0w]
    else compile_zero_words base_op ((outsz+31) DIV 32)) st = ((),final) /\
  eval_operand base_op initial = SOME (n2w p) /\ abi_decoder_operand_live st.cs_next_var base_op /\
  p+abi_empty_initialized_bytes outsz length_only < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\
    mem_bytes_at p (abi_empty_initialized_bytes outsz length_only) actual.vs_memory =
      REPLICATE (abi_empty_initialized_bytes outsz length_only) 0w /\
    abi_empty_effect st.cs_next_var p (abi_empty_initialized_bytes outsz length_only)
      limit_st initial actual
Proof
  Cases_on `length_only` >> simp_tac bool_ss [abi_empty_initialized_bytes_def] >> strip_tac
  >- (mp_tac (Q.INST [`buf` |-> `base_op:operand`, `value_op` |-> `Lit 0w`,
        `s` |-> `initial:venom_state`, `w` |-> `0w:bytes32`] abi_builtin_store_sequence) >>
      impl_tac >- (asm_simp_tac (srw_ss()) [eval_operand_def] >> decide_tac) >> strip_tac >>
      qexists_tac `mstore p 0w initial` >>
      asm_simp_tac (srw_ss()) [abi_empty_effect_def, abi_encoder_zero_word]) >>
  drule_all abi_empty_zero_words_execute >> simp[]
QED

Theorem abi_empty_complex_execute:
  compile_builtin_empty_complex outsz length_only st = (buf,final) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\
  p+abi_empty_initialized_bytes outsz length_only < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\
    eval_operand buf.buf_operand actual = SOME (n2w p) /\ buf.buf_size = outsz /\
    mem_bytes_at p (abi_empty_initialized_bytes outsz length_only) actual.vs_memory =
      REPLICATE (abi_empty_initialized_bytes outsz length_only) 0w /\
    abi_empty_effect st.cs_next_var p (abi_empty_initialized_bytes outsz length_only)
      limit_st (abi_builtin_allocate_state st.cs_next_id outsz initial) actual /\
    inst_extends st final
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_empty_complex_parts >> strip_tac >>
  drule abi_empty_alloc_buffer_shape >> strip_tac >>
  drule abi_empty_initializer_shape >> strip_tac >>
  `st.cs_next_var <= allocated.cs_next_var` by decide_tac >>
  `allocated.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`st'` |-> `allocated`, `outsz` |-> `outsz`,
    `s` |-> `initial:venom_state`] abi_builtin_alloc_buffer_frame) >>
  impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st allocated) initial = OK prepared` >>
  mp_tac (Q.INST [`st` |-> `allocated`, `base_op` |-> `buf.buf_operand`,
    `initial` |-> `prepared:venom_state`] abi_empty_initializer_execute) >>
  impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts allocated final) prepared = OK actual` >>
  `eval_operand buf.buf_operand actual = SOME (n2w p)` by
    (drule_all abi_empty_effect_operand >> simp[]) >>
  `abi_empty_effect st.cs_next_var p (abi_empty_initialized_bytes outsz length_only)
     limit_st (abi_builtin_allocate_state st.cs_next_id outsz initial) actual` by
    (drule_all abi_empty_allocation_effect >> simp[]) >>
  mp_tac (Q.INST [`st1` |-> `allocated`, `st2` |-> `final`, `s` |-> `initial:venom_state`,
    `s1` |-> `prepared:venom_state`, `s2` |-> `actual:venom_state`] abi_decode_sequence_chain) >>
  impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  qexists_tac `actual` >> asm_rewrite_tac[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_EMPTY_ALLOCATE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI Empty allocation not kernel closed: " ^ n)
  end) (DB.thms "abiEmptyAllocate");

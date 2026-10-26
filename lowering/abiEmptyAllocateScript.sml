Theory abiEmptyAllocate
Ancestors
  abiEmptyCode abiBuiltinAllocation abiDecoderReentry abiTupleEncodeSlot exprLoweringProps
  emitHelperProps compileEnv builtinSimple emitHelper venomState venomInst words list arithmetic
  abiEmptyEffect abiDecoderContract finite_map abiEmptySequence abiBuiltinEncodeFinish
  abiEncoderMemory abiDecoderGuards venomExecSemantics

(* ===== Code ===== *)

(* Structural decomposition of actual complex Empty allocation and initialization. *)

Theorem abi_empty_complex_code:
  compile_builtin_empty_complex outsz length_only st =
    let (buf,allocated) = compile_alloc_buffer outsz st in
    let (_,final) = (if length_only then emit_void MSTORE [buf.buf_operand;Lit 0w]
      else compile_zero_words buf.buf_operand ((outsz+31) DIV 32)) allocated in
      (buf,final)
Proof
  simp[compile_builtin_empty_complex_def, comp_bind_def, comp_return_def,
    comp_ignore_bind_def, LET_THM, pairTheory.UNCURRY_DEF] >>
  pairarg_tac >> Cases_on `length_only` >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> simp[]
QED

Theorem abi_empty_complex_parts:
  compile_builtin_empty_complex outsz length_only st = (buf,final) ==>
  ?allocated. compile_alloc_buffer outsz st = (buf,allocated) /\
    (if length_only then emit_void MSTORE [buf.buf_operand;Lit 0w]
      else compile_zero_words buf.buf_operand ((outsz+31) DIV 32)) allocated = ((),final)
Proof
  simp_tac bool_ss [abi_empty_complex_code, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `compile_alloc_buffer outsz st = (buf,allocated)` >>
  rename1 `_ allocated = (ignored:unit,final)` >>
  Cases_on `ignored:unit` >> gvs[] >> qexists_tac `allocated` >> simp[]
QED

Theorem abi_empty_alloc_buffer_shape:
  compile_alloc_buffer outsz st = (buf,allocated) ==>
  buf.buf_size = outsz /\ allocated.cs_next_var = st.cs_next_var+1 /\
  abi_decoder_operand_live allocated.cs_next_var buf.buf_operand /\
  inst_extends st allocated
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule abi_decoder_operand_live_emit >> strip_tac >>
  drule inst_extends_emit_op >> simp[]
QED

Theorem abi_empty_initializer_shape:
  (if length_only then emit_void MSTORE [base_op;Lit 0w]
    else compile_zero_words base_op ((outsz+31) DIV 32)) allocated = ((),final) ==>
  allocated.cs_next_var <= final.cs_next_var /\ inst_extends allocated final
Proof
  Cases_on `length_only` >> simp[] >> strip_tac
  >- (drule emitted_insts_emit_void >> strip_tac >>
      drule inst_extends_emit_void >> simp[]) >>
  drule abi_empty_zero_words_shape >> simp[]
QED

(* ===== Effect ===== *)

(* Compose the real allocator with initialization frames, including reused sites. *)

Theorem abi_empty_allocate_state_observation:
  (abi_builtin_allocate_state site outsz s).vs_memory = s.vs_memory /\
  (abi_builtin_allocate_state site outsz s).vs_call_ctx = s.vs_call_ctx /\
  (abi_builtin_allocate_state site outsz s).vs_data_section = s.vs_data_section /\
  (abi_builtin_allocate_state site outsz s).vs_halted = s.vs_halted /\
  (!op. eval_operand op (abi_builtin_allocate_state site outsz s) = eval_operand op s)
Proof
  Cases_on `FLOOKUP s.vs_allocas site = NONE` >>
  simp[abi_builtin_allocate_state_def, eval_operand_def] >>
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem abi_empty_allocation_effect:
  abi_builtin_allocation_frame first site outsz initial prepared /\
  abi_empty_effect next p written limit_st prepared actual /\ first <= next ==>
  abi_empty_effect first p written limit_st
    (abi_builtin_allocate_state site outsz initial) actual
Proof
  simp_tac bool_ss [abi_builtin_allocation_frame_def, abi_empty_effect_def] >> strip_tac >>
  `abi_decode_frame p written (abi_builtin_allocate_state site outsz initial) actual` by
    (qpat_x_assum `abi_decode_frame p written prepared actual` mp_tac >>
     asm_simp_tac bool_ss [abi_decode_frame_def, abi_empty_allocate_state_observation] >>
     strip_tac >> asm_rewrite_tac[]) >>
  asm_simp_tac bool_ss [abi_empty_allocate_state_observation] >>
  rpt gen_tac >> strip_tac >>
  `abi_decoder_operand_live next op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `first` >> simp[]) >>
  qpat_x_assum `!op w. abi_decoder_operand_live next op /\ _ ==> _` irule >>
  asm_simp_tac bool_ss [] >>
  qpat_x_assum `!op w. abi_decoder_operand_live first op /\ _ ==> _` irule >> simp[]
QED

(* ===== Empty Allocate ===== *)

(* Execute the complete Empty producer from actual allocation through zero stores.
   Reused allocations may contain arbitrary stale memory before initialization. *)

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

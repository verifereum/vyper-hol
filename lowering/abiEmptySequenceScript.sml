(* Actual execution of all ascending zero stores, with initialized byte content. *)
Theory abiEmptySequence
Ancestors
  abiEmptyCode abiEmptyWord abiEmptyMemory abiEmptyEffect abiTupleEncodeSlot
  abiTupleProps abiDecoderGuards abiDecoderContract abiDecoderReentry
  emitHelperProps exprLoweringProps compileEnv builtinSimple context
  venomState venomExecSemantics valueEncoding words list rich_list arithmetic

Theorem abi_empty_word_slot_effect:
  compile_abi_tuple_slot (ARB:compile_env) base_op off (Lit 0w)
    (BaseT (UintT 256)) st = ((),final) /\
  eval_operand base_op s = SOME (n2w p) /\ p+off < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. run_inst_seq (emitted_insts st final) s = OK actual /\ inst_extends st final /\
    mem_bytes_at (p+off) 32 actual.vs_memory = REPLICATE 32 0w /\
    abi_empty_effect st.cs_next_var (p+off) 32 limit_st s actual
Proof
  strip_tac >> drule_all abi_empty_word_slot >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) s = OK actual` >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [abi_empty_effect_def]
QED

Theorem abi_empty_zero_words_step:
  compile_zero_words base_op n st = ((),prefix_st) /\
  compile_abi_tuple_slot (ARB:compile_env) base_op (32*n) (Lit 0w)
    (BaseT (UintT 256)) prefix_st = ((),final) /\
  run_inst_seq (emitted_insts st prefix_st) initial = OK prepared /\
  mem_bytes_at p (32*n) prepared.vs_memory = REPLICATE (32*n) 0w /\
  abi_empty_effect st.cs_next_var p (32*n) limit_st initial prepared /\
  eval_operand base_op initial = SOME (n2w p) /\ abi_decoder_operand_live st.cs_next_var base_op /\
  p+32*SUC n < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\
    mem_bytes_at p (32*SUC n) actual.vs_memory = REPLICATE (32*SUC n) 0w /\
    abi_empty_effect st.cs_next_var p (32*SUC n) limit_st initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_empty_zero_words_shape >> strip_tac >>
  `eval_operand base_op prepared = SOME (n2w p)` by
    (drule_all abi_empty_effect_operand >> simp[]) >>
  `fresh_vars_wrt limit_st prepared` by
    (qpat_assum `abi_empty_effect _ _ _ _ initial prepared`
      (ACCEPT_TAC o CONJUNCT1 o PURE_REWRITE_RULE [abi_empty_effect_def])) >>
  mp_tac (Q.INST [`st` |-> `prefix_st`, `s` |-> `prepared:venom_state`,
    `off` |-> `32*n`] abi_empty_word_slot_effect) >>
  impl_tac >- (asm_rewrite_tac[] >> decide_tac) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts prefix_st final) prepared = OK actual` >>
  `abi_decode_frame (p+32*n) 32 prepared actual` by
    (qpat_assum `abi_empty_effect _ _ _ _ prepared actual`
      (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o PURE_REWRITE_RULE [abi_empty_effect_def])) >>
  `mem_bytes_at p (32*n+32) actual.vs_memory = REPLICATE (32*n+32) 0w` by
    (mp_tac (Q.INST [`p` |-> `p:num`, `m` |-> `32*n`, `n` |-> `32:num`,
      `s` |-> `prepared:venom_state`, `t` |-> `actual:venom_state`] abi_empty_prefix_extend) >>
     disch_then match_mp_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `abi_empty_effect st.cs_next_var p (32*n+32) limit_st initial actual` by
    (mp_tac (Q.INST [`first` |-> `st.cs_next_var`, `next` |-> `prefix_st.cs_next_var`,
      `m` |-> `32*n`, `n` |-> `32:num`, `s` |-> `initial:venom_state`,
      `middle` |-> `prepared:venom_state`, `t` |-> `actual:venom_state`] abi_empty_effect_append) >>
     disch_then match_mp_tac >> rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC, decide_tac]) >>
  mp_tac (Q.INST [`st1` |-> `prefix_st`, `st2` |-> `final`, `s` |-> `initial:venom_state`,
    `s1` |-> `prepared:venom_state`, `s2` |-> `actual:venom_state`] abi_decode_sequence_chain) >>
  impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  `32*SUC n = 32*n+32` by decide_tac >>
  qexists_tac `actual` >> asm_rewrite_tac[]
QED

Theorem abi_empty_zero_words_execute:
  !n base_op st final limit_st p initial.
  compile_zero_words base_op n st = ((),final) /\
  eval_operand base_op initial = SOME (n2w p) /\ abi_decoder_operand_live st.cs_next_var base_op /\
  p+32*n < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\
    mem_bytes_at p (32*n) actual.vs_memory = REPLICATE (32*n) 0w /\
    abi_empty_effect st.cs_next_var p (32*n) limit_st initial actual
Proof
  Induct >- (simp[compile_zero_words_def, comp_return_def] >> rpt strip_tac >>
    qexists_tac `initial` >>
    simp[run_inst_seq_def, emitted_insts_def, mem_bytes_at_def, abi_empty_effect_refl]) >>
  rpt gen_tac >> simp_tac bool_ss [abi_empty_zero_words_successor, LET_THM] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_zero_words base_op n st = (ignored,prefix_st)` >>
  Cases_on `ignored:unit` >> gvs[] >>
  drule abi_tuple_encode_slot_shape >> strip_tac >>
  qpat_x_assum `!base_op st final limit_st p initial. _`
    (qspecl_then [`base_op`, `st`, `prefix_st`, `limit_st`, `p`, `initial`] mp_tac) >>
  impl_tac >- (asm_rewrite_tac[] >> decide_tac) >> strip_tac >>
  drule_all abi_empty_zero_words_step >> simp[]
QED

Theory abiEmptySequence
Ancestors
  builtinSimple abiTupleProps abiTupleEncodeSlot exprLoweringProps emitHelperProps compileEnv
  context emitHelper venomState venomInst words list rich_list arithmetic abiTupleEncodeInput
  abiEncoderInput abiEncoderMemory abiDecoderReentry abiDecoderContract exprLowering
  venomExecSemantics finite_map contractABI abiDecoderFrameCompose abiDecoderArrayHeader
  valueEncoding valueEncodingProps abiEmptyEffect abiDecoderGuards
Libs
  wordsLib

(* Structural facts for the actual ascending Empty buffer initializer. *)
Theorem abi_empty_zero_words_successor:
  compile_zero_words base_op (SUC n) st =
    let (_,middle) = compile_zero_words base_op n st in
      compile_abi_tuple_slot (ARB:compile_env) base_op (n*32)
        (Lit 0w) (BaseT (UintT 256)) middle
Proof
  simp[Once compile_zero_words_def, compile_abi_tuple_slot_def, is_word_type_def,
    comp_ignore_bind_def, comp_bind_def, LET_THM, pairTheory.UNCURRY_DEF]
QED

Theorem abi_empty_zero_words_shape:
  !n base_op st final.
  compile_zero_words base_op n st = ((),final) ==>
  final.cs_next_var = st.cs_next_var+n /\
  final.cs_blocks = st.cs_blocks /\ final.cs_current_bb = st.cs_current_bb /\
  inst_extends st final
Proof
  Induct >- simp[compile_zero_words_def, comp_return_def, inst_extends_refl] >>
  rpt gen_tac >> simp_tac bool_ss [abi_empty_zero_words_successor, LET_THM] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_zero_words base_op n st = (ignored,middle)` >>
  Cases_on `ignored:unit` >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  drule abi_tuple_encode_slot_shape >> strip_tac >>
  asm_simp_tac (srw_ss()) [] >>
  conj_tac >- decide_tac >>
  irule inst_extends_trans >> qexists_tac `middle` >> simp[]
QED

(* Reuse the checked tuple word slot to execute an Empty initializer store. *)
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

(* Zeroing a buffer establishes actual bytes, including omitted array defaults. *)
Theorem abi_empty_prefix_extend:
  mem_bytes_at p m s.vs_memory = REPLICATE m 0w /\
  mem_bytes_at (p+m) n t.vs_memory = REPLICATE n 0w /\
  abi_decode_frame (p+m) n s t ==>
  mem_bytes_at p (m+n) t.vs_memory = REPLICATE (m+n) 0w
Proof
  strip_tac >>
  `mem_bytes_at p m t.vs_memory = REPLICATE m 0w` by
    (qpat_x_assum `abi_decode_frame _ _ _ _`
      (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
     disch_then (qspecl_then [`p`, `m`] mp_tac) >> simp[]) >>
  simp[Once abi_encoder_mem_split, REPLICATE_APPEND]
QED

Theorem abi_empty_store_prefix:
  mem_bytes_at p (32*n) s.vs_memory = REPLICATE (32*n) 0w ==>
  mem_bytes_at p (32*SUC n) (mstore (p+32*n) 0w s).vs_memory =
    REPLICATE (32*SUC n) 0w
Proof
  strip_tac >>
  `mem_bytes_at p (32*n) (mstore (p+32*n) 0w s).vs_memory =
    REPLICATE (32*n) 0w` by
    (mp_tac (Q.SPECL [`p`, `32*n`, `p+32*n`, `0w:bytes32`, `s`]
      mstore_mem_bytes_at_disjoint) >> simp[]) >>
  `32*SUC n = 32*n+32` by decide_tac >>
  asm_rewrite_tac[] >>
  simp_tac bool_ss [Once abi_encoder_mem_split] >>
  asm_simp_tac (srw_ss()) [abi_encoder_zero_word, REPLICATE_APPEND]
QED

Theorem abi_empty_store_frame:
  abi_decode_frame p (32*n) initial s ==>
  abi_decode_frame p (32*SUC n) initial (mstore (p+32*n) 0w s)
Proof
  strip_tac >> `32*SUC n = 32*n+32` by decide_tac >>
  asm_rewrite_tac[] >>
  irule abi_decode_frame_adjacent >> qexists_tac `s` >>
  simp[abi_decode_mstore_frame]
QED

Theorem abi_empty_zero_copy_input:
  has_type at av /\ ~is_dynamic at /\ static_length at = sz /\
  enc at av = REPLICATE sz 0w /\
  mem_bytes_at p sz mem = REPLICATE sz 0w /\ sz <= cap ==>
  abi_encoder_input (AbiCopy sz) at av p cap mem
Proof
  simp[abiEncoderInputTheory.abi_encoder_input_copy_iff]
QED

(* Actual execution of all ascending zero stores, with initialized byte content. *)
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
  irule abi_empty_zero_words_step >> simp[] >>
  qexistsl_tac [`base_op`, `prefix_st`, `actual`] >> simp[]
QED

(* Actual header/body/backedge iterations terminate at the semantic array frontier. *)
Theory abiEncoderArrayFiniteLoop
Ancestors
  abiEncoderArrayLoopStep abiEncoderArrayLoopDynamicStep abiEncoderArrayLoopHeader
  abiEncoderArrayLoopInvariant abiEncoderArrayLoopCode abiEncoderArrayCode abiEncoderArrayMemory
  abiEncoderArrayPrefix abiEncoderMembersDefs abiEncoderAdmissible abiEncoderCorrect abiDecodeRanges
  abiDecoderLoop abiDecoderEffect abiDecoderContract fragExec compileEnv
  valueEncoding contractABI venomState words list arithmetic

Theorem abi_encoder_array_loop_step:
  (if active then abi_encoder_correct ei else abi_encoder_static_leaf ei) /\
  (if active then abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz body_st = (idx,body_end)
    else abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end)) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
  abi_encoder_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) j origin initial /\
  j < LENGTH avs ==>
  ?actual. abi_encoder_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) (SUC j) origin actual /\
    abi_decode_sim ctx func initial actual
Proof
  Cases_on `active` >> simp_tac bool_ss [COND_CLAUSES] >> strip_tac >>
  FIRST [drule_all abi_encoder_array_loop_static_step, drule_all abi_encoder_array_loop_dynamic_step] >>
  asm_simp_tac bool_ss []
QED

Theorem abi_encoder_array_loop_exit:
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
  abi_encoder_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) (LENGTH avs) origin initial ==>
  ?actual. abi_encoder_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (SND (SND labels)) (LENGTH avs) origin actual /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`j` |-> `LENGTH (avs:abi_value list)`] abi_encoder_array_loop_header) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  full_simp_tac (srw_ss()) [COND_CLAUSES] >> qexists_tac `ready` >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_array_finite_loop:
  (if active then abi_encoder_correct ei else abi_encoder_static_leaf ei) /\
  (if active then abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz body_st = (idx,body_end)
    else abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end)) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
  abi_encoder_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) i origin initial ==>
  ?actual. abi_encoder_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (SND (SND labels)) (LENGTH avs) origin actual /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `i <= LENGTH avs` by (drule abi_encoder_array_loop_inv_facts >> simp[]) >>
  qabbrev_tac `loop_inv = \(j:num) (s:venom_state).
    abi_encoder_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) j origin s` >>
  qabbrev_tac `loop_post = \(s:venom_state).
    abi_encoder_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (SND (SND labels)) (LENGTH avs) origin s` >>
  mp_tac (Q.SPECL [`LENGTH (avs:abi_value list)`, `i:num`, `loop_inv`, `loop_post`, `ctx`, `func`, `initial:venom_state`]
    abi_decode_finite_iteration) >>
  impl_tac
  >- (asm_simp_tac bool_ss [Abbr`loop_inv`, Abbr`loop_post`] >> conj_tac
      >- (qx_genl_tac [`j`, `u`] >> strip_tac >>
          mp_tac (Q.INST [`j` |-> `j:num`, `initial` |-> `u:venom_state`] abi_encoder_array_loop_step) >>
          impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss []) >>
      qx_gen_tac `u` >> strip_tac >>
      mp_tac (Q.INST [`initial` |-> `u:venom_state`] abi_encoder_array_loop_exit) >>
      impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [Abbr`loop_post`]
QED

Theorem abi_encoder_array_loop_output:
  abi_encoder_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op label (LENGTH avs) origin actual ==>
  mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
  abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first site owner_st
    (LENGTH (enc (Array NONE ty) (ListV avs))-32) actual
Proof
  strip_tac >> drule abi_encoder_array_loop_inv_facts >> strip_tac >>
  qpat_assum `abi_encoder_array_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_inv_def]) >>
  qpat_assum `abi_encoder_array_memory _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_memory_def]) >>
  drule_all abi_encoder_array_prefix_complete >> disch_tac >>
  drule canonical_array_length >> strip_tac >>
  `LENGTH (enc (Array NONE ty) (ListV avs))-32 =
    LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) avs)` by
    (full_simp_tac bool_ss [] >> decide_tac) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [TAKE_LENGTH_ID]) >>
  asm_simp_tac (srw_ss()) [Excl "enc_def"]
QED

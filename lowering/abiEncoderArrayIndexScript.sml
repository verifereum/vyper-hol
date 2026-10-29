Theory abiEncoderArrayIndex
Ancestors
  abiEncoderZeroCursorPrepare abiEncoderArrayInitCode abiEncoderArrayMemory
  abiEncoderArrayCursor abiEncoderArrayPrefix abiEncoderChildInputs abiEncoderMembersDefs
  abiDecoderIndexInit abiDecoderEffect abiDecoderPrimitiveLoopFrames abiDecoderFrame
  abiDecoderContract abiDecoderReentry fragExec compileEnv valueEncoding contractABI venomState
  words list arithmetic finite_map

(* ===== Prepare ===== *)

(* Execute the actual array index allocation while retaining the processed output. *)

Theorem abi_encoder_array_memory_mono:
  abi_encoder_array_memory ei asz msz active ty avs st src dst sb source_cap d output_size b cap j s /\
  st.cs_next_var <= prepared.cs_next_var ==>
  abi_encoder_array_memory ei asz msz active ty avs prepared src dst sb source_cap d output_size b cap j s
Proof
  simp_tac bool_ss [abi_encoder_array_memory_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_buffer_pre_mono >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_array_index_prepare:
  abi_decode_index_init st = (ip,owner_st) /\ fn_has_code st owner_st func /\
  abi_encoder_array_memory ei asz msz active ty avs st src dst sb source_cap d output_size b cap j initial /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  owner_st.cs_next_id <= hi /\ hi <= last /\ owner_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready slot.
    abi_encoder_array_memory ei asz msz active ty avs owner_st src dst sb source_cap d output_size b cap j ready /\
    abi_encoder_cursor T ip st.cs_next_id slot first st.cs_next_id owner_st 0 ready /\
    abi_decoder_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap initial ready /\
    ready.vs_current_bb = owner_st.cs_current_bb /\ ready.vs_inst_idx = LENGTH owner_st.cs_current_insts /\
    ~ready.vs_halted /\ abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decode_index_init_shape >> strip_tac >>
  qpat_assum `abi_encoder_array_memory _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_memory_def]) >>
  `abi_encode_complex_prefix ([]:(abi_enc_info # num # num # bool) list) st = (ip,owner_st)` by
    asm_simp_tac bool_ss [GSYM abi_decode_index_init_complex_prefix] >>
  mp_tac (Q.INST [`ei` |-> `AbiDynArray ei asz msz active`, `at` |-> `Array NONE ty`,
    `av` |-> `ListV avs`, `cursor_op` |-> `ip`, `prepared` |-> `owner_st`]
    abi_encoder_zero_cursor_prepare) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_decoder_budget first last b cap ready` by fs[abi_decoder_effect_def] >>
  `owner_st.cs_next_id <= last` by decide_tac >>
  drule_all abi_encoder_cursor_bounds >> strip_tac >>
  `abi_decode_footprint_frame [(slot,32)] initial ready` by
    (irule abi_decoder_frame_in_footprint >> qexistsl_tac [`slot`, `32`] >> simp[]) >>
  `abi_footprint_disjoint d output_size [(slot,32)]` by
    (qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
       (assume_tac o List.last o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
     simp_tac (srw_ss()) [abi_footprint_disjoint_def] >> decide_tac) >>
  `abi_encoder_array_memory ei asz msz active ty avs st src dst sb source_cap d output_size b cap j ready` by
    (mp_tac (Q.INST [`dyn` |-> `active:bool`, `fp` |-> `[(slot,32)]`, `lo` |-> `st.cs_next_id`,
      `actual` |-> `ready:venom_state`] abi_encoder_array_memory_scratch) >>
     impl_tac >- asm_simp_tac bool_ss [abi_encoder_array_memory_def] >> asm_simp_tac bool_ss []) >>
  `st.cs_next_var <= owner_st.cs_next_var` by decide_tac >>
  drule_all abi_encoder_array_memory_mono >> strip_tac >>
  qexistsl_tac [`ready`, `slot`] >> asm_simp_tac bool_ss []
QED

(* ===== Update ===== *)

(* An index-slot write preserves the complete source/output prefix and optional tail cursor. *)

Theorem abi_encoder_array_index_update:
  abi_encoder_array_memory ei asz msz active ty avs st src dst sb source_cap d output_size b cap k initial /\
  abi_encoder_cursor T ip site slot first lo st j initial /\
  abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first lo st off initial /\
  (active ==> site < cursor_site) /\ st.cs_next_id <= last /\
  abi_decoder_budget first last b cap initial /\
  abi_decoder_effect first last site (site+1) st.cs_next_var limit_st d output_size b cap initial actual /\
  abi_decode_footprint_frame [(slot,32)] initial actual /\
  actual.vs_allocas = initial.vs_allocas /\ mload slot actual = n2w new_j ==>
  abi_encoder_array_memory ei asz msz active ty avs st src dst sb source_cap d output_size b cap k actual /\
  abi_encoder_cursor T ip site slot first lo st new_j actual /\
  abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first lo st off actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_cursor T ip _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  mp_tac (Q.INST [`cursor_op` |-> `ip:operand`, `off` |-> `j:num`, `s` |-> `initial:venom_state`]
    abi_encoder_cursor_bounds) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `abi_encoder_array_memory _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_encoder_array_memory_def]) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  `abi_footprint_disjoint d output_size [(slot,32)]` by
    (full_simp_tac (srw_ss()) [abi_footprint_disjoint_def, Excl "enc_def"] >> decide_tac) >>
  mp_tac (Q.INST [`dyn` |-> `active:bool`, `j` |-> `k:num`, `lo` |-> `site:num`, `hi` |-> `site+1`,
    `fp` |-> `[(slot:num,32:num)]`] abi_encoder_array_memory_scratch) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`cursor_op` |-> `ip:operand`, `active` |-> `T`, `off` |-> `j:num`,
    `next_off` |-> `new_j:num`, `next` |-> `st.cs_next_var`, `owned_lo` |-> `site:num`,
    `sz` |-> `output_size:num`, `owned_hi` |-> `site+1`] abi_encoder_cursor_effect_registered) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> disch_tac >>
  `abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first lo st off actual` by
    (Cases_on `active`
     >- (mp_tac (Q.INST [`active` |-> `T`, `cursor_op` |-> `dyn_ptr:operand`,
           `site` |-> `cursor_site:num`, `slot` |-> `cursor_slot:num`, `next` |-> `st.cs_next_var`,
           `sz` |-> `output_size:num`, `owned_lo` |-> `site:num`, `owned_hi` |-> `site+1`] abi_encoder_cursor_effect_protected) >>
         impl_tac >- (full_simp_tac bool_ss [abi_encoder_cursor_def] >> decide_tac) >>
         asm_simp_tac bool_ss []) >> simp[abi_encoder_cursor_def]) >>
  asm_simp_tac bool_ss []
QED

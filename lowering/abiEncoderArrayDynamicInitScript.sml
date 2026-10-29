Theory abiEncoderArrayDynamicInit
Ancestors
  abiEncoderArrayTailInit abiEncoderArrayScalarCode abiDecoderIndexInit abiDecoderContract
  fragExec compileEnv emitHelperProps venomInst words list rich_list arithmetic
  abiEncoderArrayIndex abiEncoderArrayMemory abiEncoderArrayCursor abiEncoderMembersDefs
  abiDecoderEffect abiDecoderReentry abiDecoderLoop valueEncoding contractABI venomState

(* ===== Context ===== *)

(* Exact code boundaries for the two actual dynamic-loop scratch initializers. *)

Theorem abi_encode_array_dynamic_init_trace:
  abi_encode_array_dynamic_init count_op asz start = (ptrs,owner_st) ==>
  ?ip after_index dyn_ptr.
    abi_decode_index_init start = (ip,after_index) /\
    abi_encode_array_tail_init count_op asz after_index = (dyn_ptr,owner_st) /\ ptrs = (ip,dyn_ptr)
Proof
  simp_tac bool_ss [abi_encode_array_dynamic_init_split, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `abi_decode_index_init start = (ip,after_index)` >>
  rename1 `abi_encode_array_tail_init count_op asz after_index = (dyn_ptr,prepared)` >>
  qexistsl_tac [`ip`, `after_index`, `dyn_ptr`] >> asm_simp_tac bool_ss []
QED

Theorem abi_encode_array_dynamic_init_context:
  abi_encode_array_dynamic_init count_op asz start = (ptrs,owner_st) /\ fn_has_code start owner_st func ==>
  ?ip after_index dyn_ptr.
    abi_decode_index_init start = (ip,after_index) /\
    abi_encode_array_tail_init count_op asz after_index = (dyn_ptr,owner_st) /\ ptrs = (ip,dyn_ptr) /\
    fn_has_code start after_index func /\ fn_has_code after_index owner_st func /\
    after_index.cs_next_var = start.cs_next_var+1 /\ after_index.cs_next_id = start.cs_next_id+2 /\
    owner_st.cs_next_var = start.cs_next_var+3 /\ owner_st.cs_next_id = start.cs_next_id+5
Proof
  strip_tac >> drule abi_encode_array_dynamic_init_trace >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  drule abi_encode_array_tail_init_shape >> strip_tac >>
  `cs_extends start after_index /\ cs_extends after_index owner_st` by
    (conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def, IS_PREFIX_APPEND]) >>
  mp_tac (Q.SPECL [`start`, `after_index`, `owner_st`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexistsl_tac [`ip`, `after_index`, `dyn_ptr`] >> asm_simp_tac arith_ss []
QED

(* ===== Prepare ===== *)

(* Both actual dynamic-loop initializers retain the output and distinct registered cursors. *)

Theorem abi_encoder_cursor_protected_advance:
  abi_encoder_cursor active cursor_op site slot first lo st off initial /\
  abi_decoder_effect first last owned_lo owned_hi st.cs_next_var limit_st d sz b cap initial actual /\
  st.cs_next_var <= prepared.cs_next_var /\ st.cs_next_id <= prepared.cs_next_id /\
  site < last /\ (site < owned_lo \/ owned_hi <= site) ==>
  abi_encoder_cursor active cursor_op site slot first lo prepared off actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`next` |-> `st.cs_next_var`] abi_encoder_cursor_effect_protected) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  mp_tac (Q.INST [`s` |-> `actual:venom_state`] abi_encoder_cursor_mono) >>
  impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_array_dynamic_init_prepare:
  abi_encode_array_dynamic_init count_op asz start = (ptrs,owner_st) /\ fn_has_code start owner_st func /\
  abi_encoder_array_memory ei asz msz T ty avs start src dst sb source_cap d output_size b cap 0 initial /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\ abi_decoder_operand_live start.cs_next_var count_op /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  owner_st.cs_next_id <= hi /\ hi <= last /\ owner_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?ready index_slot tail_slot.
    abi_encoder_array_memory ei asz msz T ty avs owner_st src dst sb source_cap d output_size b cap 0 ready /\
    abi_encoder_cursor T (FST ptrs) start.cs_next_id index_slot first start.cs_next_id owner_st 0 ready /\
    abi_encoder_cursor T (SND ptrs) (start.cs_next_id+2) tail_slot first start.cs_next_id owner_st
      (LENGTH avs*abi_member_head_size ty) ready /\
    abi_decoder_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial ready /\
    ready.vs_current_bb = owner_st.cs_current_bb /\ ready.vs_inst_idx = LENGTH owner_st.cs_current_insts /\
    ~ready.vs_halted /\ abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_dynamic_init_context >> strip_tac >>
  `after_index.cs_next_var <= limit_st.cs_next_var /\ after_index.cs_next_id <= hi /\
   start.cs_next_id < last /\ start.cs_next_id < after_index.cs_next_id /\
   start.cs_next_var <= after_index.cs_next_var /\ after_index.cs_next_var <= owner_st.cs_next_var /\
   after_index.cs_next_id <= owner_st.cs_next_id /\ first <= after_index.cs_next_id /\
   start.cs_next_id <= after_index.cs_next_id` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `start`, `owner_st` |-> `after_index`, `active` |-> `T`, `j` |-> `0:num`]
    abi_encoder_array_index_prepare) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_encoder_cursor T ip start.cs_next_id index_slot first start.cs_next_id after_index 0 after_index_state` >>
  qpat_assum `abi_decoder_effect _ _ _ _ _ _ _ _ _ _ initial after_index_state`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_effect_def]) >>
  `eval_operand count_op after_index_state = SOME (n2w (LENGTH avs))` by
    (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live after_index.cs_next_var count_op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `start.cs_next_var` >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`st` |-> `after_index`, `initial` |-> `after_index_state:venom_state`,
    `lo` |-> `start.cs_next_id`] abi_encoder_array_tail_init_prepare) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  rename1 `abi_encoder_cursor T dyn_ptr after_index.cs_next_id tail_slot first start.cs_next_id owner_st _ ready` >>
  `abi_encoder_cursor T ip start.cs_next_id index_slot first start.cs_next_id owner_st 0 ready` by
    (mp_tac (Q.INST [`active` |-> `T`, `cursor_op` |-> `ip`, `site` |-> `start.cs_next_id`,
      `slot` |-> `index_slot:num`, `lo` |-> `start.cs_next_id`, `st` |-> `after_index`,
      `off` |-> `0:num`, `owned_lo` |-> `after_index.cs_next_id`, `owned_hi` |-> `hi:num`,
      `prepared` |-> `owner_st`, `initial` |-> `after_index_state:venom_state`,
      `actual` |-> `ready:venom_state`, `sz` |-> `output_size:num`] abi_encoder_cursor_protected_advance) >>
     impl_tac >- asm_simp_tac (srw_ss()) [] >> asm_simp_tac bool_ss []) >>
  `abi_decoder_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap after_index_state ready` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`d`, `hi`, `after_index.cs_next_id`, `after_index.cs_next_var`, `output_size`] >>
     asm_simp_tac (srw_ss()) [] >> decide_tac) >>
  `abi_decoder_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial ready` by
    (irule abi_decoder_effect_trans >> qexists_tac `after_index_state` >> asm_simp_tac bool_ss []) >>
  qpat_assum `after_index.cs_next_id = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qexistsl_tac [`ready`, `index_slot`, `tail_slot`] >> asm_simp_tac (srw_ss()) [Excl "enc_def"] >>
  irule abi_decode_sim_trans >> qexists_tac `after_index_state` >> asm_simp_tac bool_ss []
QED

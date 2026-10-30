Theory abiEncoderArrayExit
Ancestors
  abiEncoderArrayLoopDynamicStep abiEncoderArrayLoopInvariant abiEncoderArrayLoopCode
  abiEncoderArrayCode abiEncoderArrayMemory abiEncoderArrayPrefix abiEncoderMembersDefs
  abiEncoderAdmissible abiEncoderCorrect abiDecodeRanges abiDecoderLoop abiDecoderEffect
  abiDecoderContract fragExec compileEnv valueEncoding contractABI venomState words list
  arithmetic abiEncoderArrayBodyCode abiEncoderInput abiEncoderChildInputs abiEncoderMemory
  valueEncodingProps abiEncoderSequence abiEncoderArrayContext abiEncoderBytesPrefix
  abiBuiltinPrefix abiDecoderDynamicLoopSetup abiDecoderReentryAddress abiDecoderReentry
  emitHelperProps exprLoweringProps venomExecSemantics venomInst abiEncoderPrefixReach
  abiEncoderArrayHeaderMemory

(* Actual header/body/backedge iterations terminate at the semantic array frontier. *)
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

(* ===== Inputs ===== *)

(* The complete source relation supplies the real exit reload and its semantic length. *)

Theorem abi_encoder_count_word_length:
  !payload:num. 32 <= payload ==> 32+(payload-32) = payload
Proof
  decide_tac
QED

Theorem abi_encoder_array_exit_inputs:
  abi_encoder_array_memory ei asz msz active ty avs st src dst sb source_cap d output_size b cap j s ==>
  has_type (Array NONE ty) (ListV avs) /\
  eval_operand src s = SOME (n2w sb) /\ mload sb s = n2w (LENGTH avs) /\
  asz = abi_member_head_size ty /\ active = is_dynamic ty /\ sb < dimword (:256) /\
  32 <= LENGTH (enc (Array NONE ty) (ListV avs))
Proof
  strip_tac >> drule abi_encoder_array_memory_typed >> strip_tac >>
  drule abi_encoder_array_encoding_bound >> strip_tac >>
  qpat_assum `abi_encoder_array_memory _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_memory_def]) >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  qpat_assum `abi_encoder_input _ _ _ _ _ _`
    (qx_choose_then `ct` (qx_choose_then `values` (MAP_EVERY assume_tac o CONJUNCTS)) o
      REWRITE_RULE [abi_encoder_array_input_iff]) >>
  gvs[mem_word_at_eq_mload] >> decide_tac
QED

(* ===== Sequence ===== *)

(* Execute the actual scalar exits, including the dynamic branch's discarded load. *)

Theorem abi_encode_array_static_exit_sequence:
  abi_encode_array_static_exit src asz st = (out,final) /\
  eval_operand src initial = SOME (n2w sb) /\ mload sb initial = n2w cnt /\
  sb < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial ==>
  ?actual. eval_operand out actual = SOME (n2w (32+cnt*asz)) /\
    abi_builtin_prefix st final limit_st initial actual
Proof
  simp_tac bool_ss [abi_encode_array_static_exit_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op MLOAD [src] st = (len,c1)` >>
  rename1 `emit_op MUL [len;Lit (n2w asz)] c1 = (payload,c2)` >>
  rename1 `emit_op ADD [Lit 32w;payload] c2 = (out,ready)` >>
  imp_res_tac emitted_insts_emit_op >>
  `c1.cs_next_var <= limit_st.cs_next_var /\ c2.cs_next_var <= limit_st.cs_next_var /\
   st.cs_next_var <= c1.cs_next_var /\ st.cs_next_var <= c2.cs_next_var` by decide_tac >>
  drule_all abi_builtin_emit_load >> strip_tac >>
  rename1 `abi_builtin_prefix st c1 limit_st initial loaded` >>
  `eval_operand len loaded = SOME (n2w cnt) /\ fresh_vars_wrt limit_st loaded` by
    fs[abi_builtin_prefix_def, w2n_n2w] >>
  mp_tac (Q.INST [`lhs` |-> `len`, `rhs` |-> `Lit (n2w asz)`, `out` |-> `payload`,
    `a` |-> `n2w cnt:bytes32`, `b` |-> `n2w asz:bytes32`,
    `st` |-> `c1`, `st'` |-> `c2`, `s` |-> `loaded:venom_state`] abi_builtin_emit_mul) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `abi_builtin_prefix c1 c2 limit_st loaded prepared` >>
  `abi_builtin_prefix st c2 limit_st initial prepared` by
    (irule abi_builtin_prefix_chain >> qexistsl_tac [`c1`, `loaded`] >> asm_simp_tac bool_ss []) >>
  `fresh_vars_wrt limit_st prepared` by fs[abi_builtin_prefix_def] >>
  mp_tac (Q.INST [`lhs` |-> `Lit 32w`, `rhs` |-> `payload`,
    `a` |-> `32w:bytes32`, `b` |-> `(n2w cnt:bytes32)*n2w asz`,
    `st` |-> `c2`, `st'` |-> `ready`, `s` |-> `prepared:venom_state`] abi_builtin_emit_add) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `abi_builtin_prefix c2 ready limit_st prepared actual` >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss())
    [word_add_n2w, word_mul_n2w, AC ADD_COMM ADD_ASSOC, MULT_COMM] >>
  irule abi_builtin_prefix_chain >> qexistsl_tac [`c2`, `prepared`] >> asm_simp_tac bool_ss []
QED

Theorem abi_encode_array_dynamic_exit_sequence:
  abi_encode_array_dynamic_exit src dyn_ptr st = (out,final) /\
  eval_operand src initial = SOME src_word /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ mload slot initial = n2w offset /\
  slot < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial ==>
  ?actual. eval_operand out actual = SOME (n2w (32+offset)) /\
    abi_builtin_prefix st final limit_st initial actual
Proof
  simp_tac bool_ss [abi_encode_array_dynamic_exit_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op MLOAD [src] st = (ignored,c1)` >>
  rename1 `emit_op MLOAD [dyn_ptr] c1 = (off,c2)` >>
  rename1 `emit_op ADD [Lit 32w;off] c2 = (out,ready)` >>
  imp_res_tac emitted_insts_emit_op >>
  `c1.cs_next_var <= limit_st.cs_next_var /\ c2.cs_next_var <= limit_st.cs_next_var /\
   st.cs_next_var <= c1.cs_next_var /\ st.cs_next_var <= c2.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`src` |-> `src`, `p` |-> `src_word:bytes32`, `out` |-> `ignored`,
    `st` |-> `st`, `st'` |-> `c1`, `s` |-> `initial:venom_state`] abi_builtin_emit_load) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_builtin_prefix st c1 limit_st initial loaded` >>
  `eval_operand dyn_ptr loaded = SOME (n2w slot)` by
    (irule abi_encoder_prefix_eval >> qexistsl_tac [`limit_st`, `initial`, `st`, `c1`] >>
     asm_simp_tac bool_ss []) >>
  `mload slot loaded = n2w offset /\ fresh_vars_wrt limit_st loaded` by
    fs[abi_builtin_prefix_def, abi_decoder_address_frame_def, mload_def] >>
  mp_tac (Q.INST [`src` |-> `dyn_ptr`, `p` |-> `n2w slot:bytes32`, `out` |-> `off`,
    `st` |-> `c1`, `st'` |-> `c2`, `s` |-> `loaded:venom_state`] abi_builtin_emit_load) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_builtin_prefix c1 c2 limit_st loaded prepared` >>
  `eval_operand off prepared = SOME (n2w offset) /\ fresh_vars_wrt limit_st prepared` by
    fs[abi_builtin_prefix_def, w2n_n2w] >>
  `abi_builtin_prefix st c2 limit_st initial prepared` by
    (irule abi_builtin_prefix_chain >> qexistsl_tac [`c1`, `loaded`] >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`lhs` |-> `Lit 32w`, `rhs` |-> `off`,
    `a` |-> `32w:bytes32`, `b` |-> `n2w offset:bytes32`,
    `st` |-> `c2`, `st'` |-> `ready`, `s` |-> `prepared:venom_state`] abi_builtin_emit_add) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `abi_builtin_prefix c2 ready limit_st prepared actual` >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [word_add_n2w, ADD_COMM] >>
  irule abi_builtin_prefix_chain >> qexistsl_tac [`c2`, `prepared`] >> asm_simp_tac bool_ss []
QED

(* ===== Reach ===== *)

(* Actual static and dynamic array exits return their lengths at the real CFG endpoint. *)

Theorem abi_encode_array_static_exit_reach:
  abi_encode_array_static_exit src asz st = (out,final) /\ fn_has_code st final func /\
  eval_operand src initial = SOME (n2w sb) /\ mload sb initial = n2w cnt /\
  sb < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w (32+cnt*asz)) /\ fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule (CONJUNCT1 abi_encode_array_exit_shape) >> strip_tac >>
  drule_all abi_encode_array_static_exit_sequence >> strip_tac >>
  drule_all abi_encoder_prefix_reach >> simp[]
QED

Theorem abi_encode_array_dynamic_exit_reach:
  abi_encode_array_dynamic_exit src dyn_ptr st = (out,final) /\ fn_has_code st final func /\
  eval_operand src initial = SOME src_word /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ mload slot initial = n2w offset /\
  slot < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w (32+offset)) /\ fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule (CONJUNCT2 abi_encode_array_exit_shape) >> strip_tac >>
  drule_all abi_encode_array_dynamic_exit_sequence >> strip_tac >>
  drule_all abi_encoder_prefix_reach >> simp[]
QED

(* ===== Correct ===== *)

(* Connect both real exit sequences to the completed array invariant. *)

Theorem abi_encoder_array_exit_reach:
  abi_encoder_array_memory ei asz msz active ty avs owner_st src dst sb source_cap d output_size b cap j initial /\
  abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first site owner_st
    (LENGTH (enc (Array NONE ty) (ListV avs))-32) initial /\
  (if active then abi_encode_array_dynamic_exit src dyn_ptr st = (out,final)
    else abi_encode_array_static_exit src asz st = (out,final)) /\
  fn_has_code st final func /\ owner_st.cs_next_var <= st.cs_next_var /\ owner_st.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_decoder_budget first last b cap initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_array_exit_inputs >> strip_tac >>
  Cases_on `active` >> full_simp_tac bool_ss [COND_CLAUSES]
  >- (drule_all abi_encoder_cursor_bounds >> strip_tac >>
      qpat_assum `abi_encoder_cursor T _ _ _ _ _ _ _ _`
        (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
      `abi_decoder_operand_live st.cs_next_var dyn_ptr` by
        (irule abi_decoder_operand_live_mono >> qexists_tac `owner_st.cs_next_var` >>
         asm_simp_tac bool_ss []) >>
      qpat_assum `32 <= LENGTH _` (assume_tac o MATCH_MP abi_encoder_count_word_length) >>
      mp_tac (Q.INST [`src_word` |-> `n2w sb:bytes32`, `slot` |-> `cursor_slot:num`,
        `offset` |-> `LENGTH (enc (Array NONE ty) (ListV avs))-32`]
        abi_encode_array_dynamic_exit_reach) >>
      impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss []) >>
  `LENGTH (enc (Array NONE ty) (ListV avs)) = 32+LENGTH avs*asz` by
    (drule_all abi_encoder_array_static_size >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`cnt` |-> `LENGTH (avs:abi_value list)`] abi_encode_array_static_exit_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_array_loop_scalar_exit:
  abi_encoder_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op label (LENGTH avs) origin initial /\
  (if active then abi_encode_array_dynamic_exit src dyn_ptr st = (out,final)
    else abi_encode_array_static_exit src asz st = (out,final)) /\
  fn_has_code st final func /\ owner_st.cs_next_var <= st.cs_next_var /\ owner_st.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\
  label = st.cs_current_bb /\ st.cs_current_insts = [] ==>
  ?actual.
    mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_decoder_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap origin actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_array_loop_output >> strip_tac >>
  drule abi_encoder_array_loop_inv_facts >> strip_tac >>
  qpat_assum `abi_encoder_array_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_inv_def]) >>
  mp_tac (Q.INST [`j` |-> `LENGTH (avs:abi_value list)`] abi_encoder_array_exit_reach) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`,
    `next` |-> `owner_st.cs_next_var`, `child_next` |-> `st.cs_next_var`,
    `lo` |-> `site:num`, `sz` |-> `output_size:num`] abi_decoder_address_effect) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_decoder_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap origin actual` by
    (irule abi_decoder_effect_trans >> qexists_tac `initial` >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> full_simp_tac bool_ss [abi_decoder_address_frame_def]
QED

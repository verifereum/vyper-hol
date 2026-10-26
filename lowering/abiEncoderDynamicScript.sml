Theory abiEncoderDynamic
Ancestors
  abiEncoderChildPrefix abiEncoderChildCode abiEncoderChildInputs abiEncoderCorrect
  abiDecoderEffect abiDecoderArrayInitExec abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecoderContract abiDecoderLoop fragExec compileEnv valueEncoding venomState words list
  arithmetic abiDecoderAllocation finite_map abiEncoderChildSuffixReach abiEncoderChildEffect
  abiDecoderProtectedScratch venomExecSemantics pred_set abiEncoderChildContext
  abiEncoderChildCompose abiEncoderChildFrames abiEncoder

(* ===== Child Prepare ===== *)

(* Establish the recursive child's pure precondition after emitted dynamic setup. *)

Theorem abi_encoder_dynamic_child_prepare:
  abi_encode_child_prefix dst head_offset dyn_ptr st = (ops,prepared) /\ fn_has_code st prepared func /\
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap initial /\
  eval_operand dyn_ptr initial = SOME (n2w slot) /\ mload slot initial = n2w off /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ slot < dimword (:256) /\
  off+LENGTH (enc at av) <= output_size /\ abi_decoder_budget first last b cap initial /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready. abi_encoder_pre ei at av prepared src (SND (SND ops))
      sb source_cap (d+off) b cap ready /\
    eval_operand (FST ops) ready = SOME (n2w (d+head_offset)) /\
    eval_operand (FST (SND ops)) ready = SOME (n2w off) /\
    abi_decoder_operand_live prepared.cs_next_var (FST ops) /\
    abi_decoder_operand_live prepared.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live prepared.cs_next_var (SND (SND ops)) /\
    fresh_vars_wrt limit_st ready /\ abi_decoder_budget first last b cap ready /\
    abi_decoder_address_frame st.cs_next_var initial ready /\
    ready.vs_current_bb = prepared.cs_current_bb /\ ready.vs_inst_idx = LENGTH prepared.cs_current_insts /\
    ~ready.vs_halted /\ abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  drule abi_encode_child_prefix_shape >> strip_tac >>
  drule abi_encode_child_prefix_live >> strip_tac >>
  mp_tac (Q.INST [`st'` |-> `prepared`, `db` |-> `d:num`] abi_encode_child_prefix_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  `st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  `abi_encoder_pre ei at av prepared src (SND (SND ops)) sb source_cap (d+off) b cap ready` by
    (mp_tac (Q.INST [`child_st` |-> `prepared`, `child_dst` |-> `SND (SND (ops:operand # operand # operand))`,
      `actual` |-> `ready:venom_state`, `offset` |-> `off:num`] abi_encoder_child_pre_address) >>
     asm_simp_tac bool_ss []) >>
  `abi_decoder_budget first last b cap ready` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `ready:venom_state`]
      abi_decoder_budget_transport) >>
     impl_tac >- fs[abi_decoder_address_frame_def] >> asm_simp_tac bool_ss []) >>
  qexists_tac `ready` >> asm_simp_tac bool_ss []
QED

(* ===== Child Core ===== *)

(* Recursive core execution preserves the child's saved head/offset and parent cursor. *)

Theorem abi_encoder_effect_operand:
  abi_decoder_effect first last lo hi next limit_st d sz b cap s t /\
  abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
  eval_operand op t = SOME w
Proof
  simp_tac bool_ss [abi_decoder_effect_def] >> strip_tac >> first_x_assum irule >> simp[]
QED

Theorem abi_encoder_dynamic_child_core:
  abi_encoder_correct ei /\ compile_abi_encode_to_buf dst src ei start = (out,end_st) /\
  fn_has_code start end_st func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_pre ei at av start src dst sb source_cap d b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_decoder_operand_live start.cs_next_var head /\ abi_decoder_operand_live start.cs_next_var offset /\
  abi_decoder_operand_live start.cs_next_var dyn_ptr /\
  eval_operand head initial = SOME (n2w h) /\ eval_operand offset initial = SOME (n2w off) /\
  eval_operand dyn_ptr initial = SOME (n2w slot) /\
  first <= site /\ site < last /\ site < start.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?t. mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    abi_decoder_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
      limit_st d (LENGTH (enc at av)) b cap initial t /\
    eval_operand head t = SOME (n2w h) /\ eval_operand offset t = SOME (n2w off) /\
    eval_operand dyn_ptr t = SOME (n2w slot) /\ FLOOKUP t.vs_allocas site = SOME (slot,32) /\
    mload slot t = mload slot initial /\ fresh_vars_wrt limit_st t /\ abi_decoder_budget first last b cap t /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_correct_run >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  mp_tac (Q.INST [`lo` |-> `start.cs_next_id`, `hi` |-> `end_st.cs_next_id`,
    `next` |-> `start.cs_next_var`, `sz` |-> `LENGTH (enc at av)`,
    `s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`] abi_decoder_effect_protected_slot) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  imp_res_tac abi_encoder_effect_operand >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >> fs[abi_decoder_effect_def]
QED

(* ===== Child Finish ===== *)

(* Actual final stores preserve the recursively encoded tail and update its head/cursor. *)

Theorem abi_encoder_dynamic_child_finish:
  abi_encode_child_suffix head dyn_ptr offset child_len st = (out,st') /\ fn_has_code st st' func /\
  eval_operand head initial = SOME (n2w h) /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  eval_operand offset initial = SOME (n2w off) /\ eval_operand child_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ abi_decoder_operand_live st.cs_next_var child_len /\
  mem_bytes_at (d+off) len initial.vs_memory = bytes /\
  d <= h /\ h+32 <= d+off /\ off+len <= output_size /\
  d+output_size < dimword (:256) /\ (d+output_size <= b \/ b+cap <= d) /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < last /\
  lo <= site /\ site < hi /\ FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. mem_bytes_at (d+off) len t.vs_memory = bytes /\
    mem_word_at h t.vs_memory = n2w off /\ mem_word_at slot t.vs_memory = n2w (off+len) /\
    eval_operand out t = SOME (n2w len) /\
    abi_decode_footprint_frame [(h,32);(slot,32)] initial t /\
    FLOOKUP t.vs_allocas site = SOME (slot,32) /\
    abi_decoder_effect first last lo hi st.cs_next_var limit_st d output_size b cap initial t /\
    t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `site IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  qpat_assum `abi_decoder_budget _ _ _ _ _`
    (assume_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decoder_budget_def]) >>
  `h < dimword (:256) /\ slot < dimword (:256) /\ h+32 <= d+output_size` by decide_tac >>
  mp_tac (Q.INST [`p` |-> `slot:num`] abi_encode_child_suffix_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  mp_tac (Q.INST [`q` |-> `d+off`, `offset` |-> `off:num`] abi_encoder_child_suffix_output) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  mp_tac (Q.INST [`sz` |-> `output_size:num`, `off` |-> `off:num`]
    abi_encoder_child_suffix_effect) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >> fs[abi_encoder_child_suffix_post_def]
QED

(* ===== Child ===== *)

(* Execute the actual dynamic-child wrapper using only the recursive core contract. *)

Theorem abi_encoder_dynamic_child_reach:
  abi_encoder_correct ei /\ compile_abi_encode_child dst src ei T head_offset dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap initial /\
  eval_operand dyn_ptr initial = SOME (n2w slot) /\ mload slot initial = n2w off /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\
  head_offset+32 <= off /\ off+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < st.cs_next_id /\ lo <= site /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. mem_bytes_at (d+off) (LENGTH (enc at av)) t.vs_memory = enc at av /\
    mem_word_at (d+head_offset) t.vs_memory = n2w off /\
    mem_word_at slot t.vs_memory = n2w (off+LENGTH (enc at av)) /\
    FLOOKUP t.vs_allocas site = SOME (slot,32) /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    abi_decode_footprint_frame [(d+head_offset,32);(d+off,LENGTH (enc at av));(b,cap)] initial t /\
    abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial t /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_dynamic_child_context >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var /\ child_end.cs_next_var <= limit_st.cs_next_var /\
    first <= prepared.cs_next_id /\ child_end.cs_next_id <= last /\ site < last /\
    site < prepared.cs_next_id /\ st.cs_next_var <= prepared.cs_next_var /\
    st.cs_next_var <= child_end.cs_next_var` by decide_tac >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  `site IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  qpat_assum `abi_decoder_budget _ _ _ _ _`
    (assume_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decoder_budget_def]) >>
  `slot < dimword (:256)` by decide_tac >>
  mp_tac abi_encoder_dynamic_child_prepare >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  `abi_decoder_operand_live prepared.cs_next_var dyn_ptr /\
    abi_decoder_operand_live child_end.cs_next_var dyn_ptr` by
    (conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `FLOOKUP ready.vs_allocas site = SOME (slot,32) /\ eval_operand dyn_ptr ready = SOME (n2w slot)`
    by fs[abi_decoder_address_frame_def] >>
  mp_tac (Q.INST [`start` |-> `prepared`, `end_st` |-> `child_end`, `initial` |-> `ready:venom_state`,
    `dst` |-> `SND (SND (ops:operand # operand # operand))`, `out` |-> `child_len`, `d` |-> `d+off`,
    `head` |-> `FST (ops:operand # operand # operand)`, `offset` |-> `FST (SND (ops:operand # operand # operand))`,
    `h` |-> `d+head_offset`] abi_encoder_dynamic_child_core) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> fs[Excl "enc_def"]) >> strip_tac >>
  rename1 `abi_decode_sim ctx func ready encoded` >>
  mp_tac (Q.INST [`st` |-> `child_end`, `st'` |-> `end_st`, `initial` |-> `encoded:venom_state`,
    `head` |-> `FST (ops:operand # operand # operand)`, `offset` |-> `FST (SND (ops:operand # operand # operand))`,
    `h` |-> `d+head_offset`, `len` |-> `LENGTH (enc at av)`, `bytes` |-> `enc at av`,
    `hi` |-> `end_st.cs_next_id`] abi_encoder_dynamic_child_finish) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  rename1 `abi_decode_sim ctx func encoded actual` >>
  `abi_decode_footprint_frame [(d+head_offset,32);(d+off,LENGTH (enc at av));(b,cap)] initial actual` by
    (mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `h` |-> `d+head_offset`, `q` |-> `d+off`,
      `len` |-> `LENGTH (enc at av)`] abi_encoder_dynamic_child_frame) >>
     impl_tac >- fs[abi_decoder_effect_def] >> simp[]) >>
  mp_tac (Q.INST [`child_lo` |-> `prepared.cs_next_id`, `child_hi` |-> `child_end.cs_next_id`,
    `child_next` |-> `prepared.cs_next_var`, `suffix_next` |-> `child_end.cs_next_var`,
    `child_d` |-> `d+off`, `child_sz` |-> `LENGTH (enc at av)`, `sz` |-> `output_size:num`,
    `next` |-> `st.cs_next_var`, `hi` |-> `end_st.cs_next_id`] abi_encoder_child_compose) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

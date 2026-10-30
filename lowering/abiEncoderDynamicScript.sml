Theory abiEncoderDynamic
Ancestors
  abiEncoderMemberSourceAdapter abiEncoderChildPrefix abiEncoderChildCode abiEncoderChildInputs abiEncoderCorrect
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

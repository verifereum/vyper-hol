Theory abiScratchStatic
Ancestors
  abiScratchMemberAdapter abiScratchEncoderRun abiScratchChild abiScratchAfterAddress abiScratchAddress
  abiScratchFrameCompose abiScratchEncoderContract abiScratchFootprint abiEncoderStatic
  abiEncoderAddressReach abiEncoderChildFrames abiDecoderDynamicLoopSetup abiDecoderAllocation
  abiDecoderFootprint abiDecoderFrame abiDecoderReentry abiDecoderContract abiDecoderLoop
  compileEnv valueEncoding contractABI venomState pred_set words list arithmetic
  abiScratchEncoderLeaves abiScratchEffect abiEncoderAdmissible abiEncoderLeafCode
  abiDecoderCorrectWord abiEncoderArrayFrame abiEncoderArrayBounds abiEncoderArrayPrefix
  abiEncoderArrayLayout abiEncoderTuple abiEncoderMemory abiCanonicalWindows valueEncodingProps
  rich_list

(* ===== Child ===== *)

(* Execute a member's static placement under its recursive child hypothesis.
   TOP-LEVEL: abi_scratch_static_child_reach follows the actual head ADD and
   child encoder, retaining its narrow physical write frame. *)

Theorem abi_scratch_child_frame_after_address:
  abi_decoder_address_frame next initial ready /\
  abi_scratch_effect first last child_lo hi child_next limit_st d sz b cap ready actual /\
  lo <= child_lo ==>
  abi_decode_footprint_frame
    ([(d,sz)] ++ abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial) initial actual
Proof
  strip_tac >>
  `abi_decoder_ids child_lo hi SUBSET abi_decoder_ids lo hi` by
    (simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >>
  `abi_decode_footprint_frame
    ([(d,sz)] ++ abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap ready) ready actual` by
    (mp_tac (Q.INST [`ids` |-> `abi_decoder_ids lo hi`,
       `child_ids` |-> `abi_decoder_ids child_lo hi`, `fp` |-> `[(d,sz)]`,
       `s` |-> `ready:venom_state`, `t` |-> `actual:venom_state`] abi_scratch_frame_subset_append) >>
     impl_tac >- (asm_simp_tac (srw_ss()) [] >> fs[abi_scratch_effect_def]) >> simp[]) >>
  drule_all abi_scratch_frame_after_address >> simp[]
QED

Theorem abi_scratch_static_child_reach:
  abi_scratch_encoder ei /\ compile_abi_encode_child dst src ei F offset dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_input ei at av st src dst sb source_cap d output_size first last b cap initial /\
  offset+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at (d+offset) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_decode_footprint_frame
      ([(d+offset,LENGTH (enc at av))] ++ abi_decoder_child_scratch
        (abi_decoder_ids st.cs_next_id end_st.cs_next_id) b cap initial) initial actual /\
    abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  MATCH_ACCEPT_TAC abiScratchMemberAdapterTheory.abi_scratch_static_child_spine_reach
QED

(* ===== Info ===== *)

(* Execute the actual static child helper under the precise encoder contract.
   TOP-LEVEL: abi_scratch_static_info_reach returns the exact child window and
   an enclosing physical effect. Helpers select a bounded destination and
   derive the contract for word/copy/empty static leaves. *)

Theorem abi_scratch_static_leaf:
  abi_encoder_static_leaf ei ==> abi_scratch_encoder ei
Proof
  rw[abi_encoder_static_leaf_def] >>
  simp[abi_scratch_encoder_word, abi_scratch_encoder_copy, abi_scratch_encoder_empty]
QED

Theorem abi_scratch_input_offset:
  abi_scratch_input ei at av st src dst sb source_cap d output_size first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ abi_decoder_operand_live st.cs_next_var head /\
  eval_operand head initial = SOME (n2w (d+offset)) /\ offset+LENGTH (enc at av) <= output_size ==>
  abi_scratch_input ei at av st src head sb source_cap (d+offset) (LENGTH (enc at av))
    first last b cap initial
Proof
  strip_tac >>
  `abi_decoder_address_frame st.cs_next_var initial initial` by simp[abi_decoder_address_frame_def] >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap initial initial` by
    (irule abi_scratch_evolution_refl >> drule abi_decoder_budget_frontier >> simp[]) >>
  mp_tac (Q.INST [`prepared` |-> `st:compile_state`, `actual` |-> `initial:venom_state`,
    `child_dst` |-> `head:operand`, `off` |-> `offset:num`] abi_scratch_child_input_address) >>
  asm_simp_tac bool_ss [LESS_EQ_REFL]
QED

Theorem abi_scratch_static_info_reach:
  abi_encoder_static_leaf ei /\ compile_abi_encode_static_info head src ei st = (out,end_st) /\
  fn_has_code st end_st func /\
  abi_scratch_input ei at av st src dst sb source_cap d output_size first last b cap initial /\
  abi_decoder_operand_live st.cs_next_var head /\
  eval_operand head initial = SOME (n2w (d+offset)) /\ offset+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at (d+offset) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_decode_footprint_frame
      ((d+offset,LENGTH (enc at av))::abi_decoder_child_scratch
        (abi_decoder_ids st.cs_next_id end_st.cs_next_id) b cap initial) initial actual /\
    abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_scratch_static_leaf >> disch_tac >>
  qpat_assum `abi_encoder_static_leaf ei` (fn th =>
    qpat_assum `compile_abi_encode_static_info _ _ _ _ = _`
      (assume_tac o PURE_REWRITE_RULE [MATCH_MP abi_encode_static_info_agrees th])) >>
  drule_all abi_encode_static_leaf_shape >> strip_tac >>
  drule_all abi_scratch_input_offset >> disch_tac >>
  mp_tac (Q.INST [`start` |-> `st`, `dst` |-> `head:operand`, `d` |-> `d+offset`]
    abi_scratch_encoder_run) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d+offset`, `end_st.cs_next_id`, `st.cs_next_id`, `st.cs_next_var`, `LENGTH (enc at av)`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

(* ===== Step ===== *)

(* A static child extends the output prefix while preserving physical scratch.
   TOP-LEVEL: abi_scratch_array_static_step advances the count/head invariant.
   Helpers: single-head write separation and tuple prefix extension. *)

Theorem abi_scratch_static_prefix_windows:
  heads+head_sz <= hl /\ hl+tails <= output_size /\ abi_footprint_disjoint d output_size fp ==>
  abi_footprint_disjoint d heads ((d+heads,head_sz)::fp) /\
  abi_footprint_disjoint (d+hl) tails ((d+heads,head_sz)::fp)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_footprint_disjoint d heads fp /\ abi_footprint_disjoint (d+hl) tails fp` by
    (conj_tac >> irule abi_footprint_disjoint_subwindow >>
     qexistsl_tac [`d`, `output_size`] >> asm_simp_tac bool_ss [] >> decide_tac) >>
  asm_simp_tac bool_ss [abi_scratch_disjoint_cons] >> decide_tac
QED

Theorem abi_scratch_tuple_static_step:
  LENGTH pre = LENGTH pvs /\ ~is_dynamic ty /\
  heads = LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs)) /\
  tails = LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  heads+LENGTH (enc ty av) <= hl /\ hl+tails <= output_size /\
  abi_footprint_disjoint d output_size fp /\
  abi_encoder_tuple_prefix hl pre pvs d initial.vs_memory /\
  abi_decode_footprint_frame ((d+heads,LENGTH (enc ty av))::fp) initial actual /\
  mem_bytes_at (d+heads) (LENGTH (enc ty av)) actual.vs_memory = enc ty av ==>
  abi_encoder_tuple_prefix hl (pre++[ty]) (pvs++[av]) d actual.vs_memory
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`head_sz` |-> `LENGTH (enc ty av)`] abi_scratch_static_prefix_windows) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`fp` |-> `(d+heads,LENGTH (enc ty av))::fp`] abi_encoder_tuple_prefix_frame) >>
  impl_tac >- gvs[Excl "enc_def"] >> strip_tac >>
  mp_tac (Q.INST [`mem` |-> `actual.vs_memory`] abi_encoder_tuple_prefix_append) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> gvs[Excl "enc_def", mem_bytes_at_def]) >> simp[]
QED

Theorem abi_scratch_array_static_step:
  has_type (Array NONE ty) (ListV avs) /\ j < LENGTH avs /\ ~is_dynamic ty /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\ abi_footprint_disjoint d output_size fp /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_decode_footprint_frame ((d+32+j*abi_member_head_size ty,LENGTH (enc ty (EL j avs)))::fp) initial actual /\
  mem_bytes_at (d+32+j*abi_member_head_size ty) (LENGTH (enc ty (EL j avs))) actual.vs_memory = enc ty (EL j avs) ==>
  abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_array_child_bounds >> strip_tac >>
  `j <= LENGTH avs` by decide_tac >> drule_all abi_encoder_array_prefix_sizes >> strip_tac >>
  `LENGTH (TAKE j avs) = j` by simp[] >>
  `abi_footprint_disjoint d 32 fp /\ abi_footprint_disjoint (d+32) (output_size-32) fp` by
    (conj_tac >> irule abi_footprint_disjoint_subwindow >>
     qexistsl_tac [`d`, `output_size`] >> asm_simp_tac bool_ss [] >> decide_tac) >>
  qpat_assum `abi_encoder_array_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_prefix_def]) >>
  `mload d actual = mload d initial` by
    (irule abi_decode_footprint_frame_mload >>
     qexists_tac `(d+32+j*abi_member_head_size ty,LENGTH (enc ty (EL j avs)))::fp` >>
     asm_simp_tac (srw_ss()) [abi_scratch_disjoint_cons] >> decide_tac) >>
  `mem_word_at d actual.vs_memory = n2w (LENGTH avs)` by full_simp_tac bool_ss [mem_word_at_eq_mload] >>
  mp_tac (Q.INST [`pre` |-> `REPLICATE j ty`, `pvs` |-> `TAKE j (avs:abi_value list)`,
    `av` |-> `EL j (avs:abi_value list)`, `heads` |-> `j*abi_member_head_size ty`,
    `tails` |-> `SUM (MAP (abi_member_tail_size ty) (TAKE j (avs:abi_value list)))`,
    `hl` |-> `LENGTH (avs:abi_value list)*abi_member_head_size ty`, `d` |-> `d+32`,
    `output_size` |-> `output_size-32`] abi_scratch_tuple_static_step) >>
  impl_tac >- (full_simp_tac bool_ss [LENGTH_REPLICATE] >> decide_tac) >> disch_tac >>
  irule abi_encoder_array_prefix_advance >> asm_simp_tac bool_ss []
QED

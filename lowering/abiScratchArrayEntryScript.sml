(* Precise frames for the complete dynamic-array parent initializer.
   Helpers transport source data, cursor contents and allocation metadata.
   TOP-LEVEL: abi_scratch_array_entry composes the actual cursor initializer
   and count copy in their containing function, including allocation reuse. *)
Theory abiScratchArrayEntry
Ancestors
  abiScratchPrefixReach abiScratchArrayCount abiScratchFootprint abiCallerAllocation
  abiEncoderArrayParent abiEncoderComplexPrefix abiEncoderArrayCount abiEncoderMembersDefs
  abiEncoderInputFrame abiEncoderInput abiDecoderPrimitiveLoopFrames abiDecoderFrameCompose
  abiDecoderFrame abiDecoderContract abiDecoderReentry abiDecoderAllocation abiDecoderFootprint
  abiDecoderLoop abiDecoderArrayInitExec compileEnv valueEncoding valueEncodingProps contractABI
  venomState finite_map pred_set words list arithmetic

Theorem abi_scratch_frame_cons:
  abi_decode_footprint_frame fp s t ==>
  abi_decode_footprint_frame ((d,sz)::fp) s t
Proof
  rw[abi_decode_footprint_frame_def] >> first_x_assum irule >>
  fs[abi_scratch_disjoint_cons]
QED

Theorem abi_scratch_array_entry_frame:
  abi_decode_footprint_frame fp initial prepared /\
  abi_decode_frame d 32 prepared actual ==>
  abi_decode_footprint_frame ((d,32)::fp) initial actual
Proof
  strip_tac >> irule abi_decode_footprint_frame_trans >> qexists_tac `prepared` >> conj_tac
  >- (drule_all abi_scratch_frame_cons >> simp[]) >>
  irule abi_decoder_frame_in_footprint >> qexistsl_tac [`d`, `32`] >> simp[]
QED

Theorem abi_scratch_prefix_data:
  abi_encoder_complex_prefix_post infos dyn_ptr next site limit_st first last b cap initial prepared /\
  abi_encoder_input ei at av sb source_cap initial.vs_memory /\
  abi_decode_footprint_frame fp initial prepared /\ abi_footprint_disjoint sb source_cap fp /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst ==>
  abi_encoder_input ei at av sb source_cap prepared.vs_memory /\
  eval_operand src prepared = SOME (n2w sb) /\ eval_operand dst prepared = SOME (n2w d)
Proof
  strip_tac >> drule_all abi_encoder_input_frame >> disch_then assume_tac >>
  qpat_x_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
  qpat_assum `!op. _` (qspec_then `src` mp_tac) >>
  qpat_assum `!op. _` (qspec_then `dst` mp_tac) >> simp[]
QED

Theorem abi_scratch_array_entry_metadata:
  abi_scratch_evolution ids b cap initial prepared /\
  abi_decoder_budget first last b cap prepared /\
  actual.vs_allocas = prepared.vs_allocas /\ actual.vs_alloca_next = prepared.vs_alloca_next ==>
  abi_scratch_evolution ids b cap initial actual /\ abi_decoder_budget first last b cap actual
Proof
  strip_tac >>
  `(abi_scratch_evolution ids b cap initial actual <=>
    abi_scratch_evolution ids b cap initial prepared)` by
    (irule abi_scratch_evolution_transport >> simp[]) >>
  `(abi_decoder_budget first last b cap actual <=>
    abi_decoder_budget first last b cap prepared)` by
    (irule abi_decoder_budget_transport >> simp[]) >>
  asm_rewrite_tac[]
QED

Theorem abi_scratch_prefix_operands:
  abi_encoder_complex_prefix_post infos dyn_ptr next site limit_st first last b cap initial prepared /\
  next <= owner_next /\
  (!op w. abi_decoder_operand_live owner_next op /\ eval_operand op prepared = SOME w ==>
    eval_operand op actual = SOME w) ==>
  !op w. abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
    eval_operand op actual = SOME w
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
  `eval_operand op prepared = SOME w` by
    (qpat_x_assum `!op. _` (qspec_then `op` mp_tac) >> simp[]) >>
  `abi_decoder_operand_live owner_next op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >>
  qpat_x_assum `!op w. _` drule_all >> simp[]
QED

Theorem abi_scratch_array_entry_cursor:
  abi_encoder_complex_prefix_post ([]:(abi_enc_info # num # num # bool) list)
    parent_ptr next site limit_st first last b cap initial prepared /\
  abi_scratch_evolution ids b cap initial prepared /\ FINITE ids /\ site IN ids /\
  abi_footprint_disjoint d 32 (abi_decoder_child_scratch ids b cap initial) /\
  abi_decode_frame d 32 prepared actual /\ actual.vs_allocas = prepared.vs_allocas /\
  (!op w. abi_decoder_operand_live owner_next op /\ eval_operand op prepared = SOME w ==>
    eval_operand op actual = SOME w) /\
  abi_decoder_operand_live owner_next parent_ptr /\
  abi_decoder_operand_live loop_st.cs_next_var parent_ptr /\
  first <= site /\ site < loop_st.cs_next_id ==>
  ?slot. abi_encoder_cursor T parent_ptr site slot first site loop_st 0 actual
Proof
  strip_tac >>
  qpat_x_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
  rename1 `FLOOKUP prepared.vs_allocas site = SOME (slot,32)` >>
  drule_all abi_scratch_disjoint_advance >> disch_then assume_tac >>
  `MEM (slot,32) (abi_decoder_child_scratch ids b cap prepared)` by
    (irule abi_scratch_registered_member >> asm_simp_tac bool_ss [] >>
     qexists_tac `site` >> simp[]) >>
  `mload slot actual = mload slot prepared` by
    (mp_tac (Q.INST [`s` |-> `prepared:venom_state`, `t` |-> `actual:venom_state`,
       `p` |-> `slot`, `d` |-> `d:num`, `sz` |-> `32`] abi_decode_frame_mem_word) >>
     impl_tac >- (asm_rewrite_tac[] >>
       qpat_x_assum `abi_footprint_disjoint _ _ _`
         (qspecl_then [`slot`, `32`] mp_tac o REWRITE_RULE [abi_footprint_disjoint_def]) >>
       simp[] >> decide_tac) >> simp[mem_word_at_eq_mload]) >>
  `eval_operand parent_ptr actual = SOME (n2w slot)` by
    (qpat_x_assum `!op w. _` (qspecl_then [`parent_ptr`, `n2w slot:bytes32`] mp_tac) >> simp[]) >>
  qexists_tac `slot` >> simp[abi_encoder_cursor_def]
QED

Theorem abi_scratch_array_entry:
  abi_encode_array_prefix src dst st = (ops,loop_st) /\ fn_has_code st loop_st func /\
  abi_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    sb source_cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  abi_decoder_budget first last b cap initial /\ st.cs_next_id IN abi_decoder_ids first last /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  FINITE ids /\ st.cs_next_id IN ids /\
  abi_footprint_disjoint sb source_cap (abi_decoder_child_scratch ids b cap initial) /\
  abi_footprint_disjoint d 32 (abi_decoder_child_scratch ids b cap initial) /\
  abi_footprint_disjoint sb source_cap [(d,32)] /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot.
    abi_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
      sb source_cap actual.vs_memory /\
    abi_encoder_array_prefix ty avs 0 d actual.vs_memory /\
    abi_encoder_cursor T (FST ops) st.cs_next_id slot first st.cs_next_id loop_st 0 actual /\
    eval_operand (SND ops) actual = SOME (n2w (LENGTH avs)) /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_budget first last b cap actual /\
    abi_scratch_evolution ids b cap initial actual /\
    abi_decode_footprint_frame ((d,32)::abi_decoder_child_scratch ids b cap initial) initial actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = loop_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  strip_tac >> drule_all abi_encode_array_prefix_context >> strip_tac >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  `allocated.cs_next_var <= limit_st.cs_next_var /\
   st.cs_next_var <= allocated.cs_next_var /\ allocated.cs_next_var <= loop_st.cs_next_var` by decide_tac >>
  drule_all abi_scratch_encoder_prefix_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  drule_all abi_scratch_prefix_data >> strip_tac >>
  `abi_decoder_operand_live allocated.cs_next_var dst` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `fresh_vars_wrt limit_st prepared /\ abi_decoder_budget first last b cap prepared` by
    fs[abi_encoder_complex_prefix_post_def] >>
  drule_all (Q.INST [`initial` |-> `prepared:venom_state`] abi_scratch_array_count_reach) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func prepared actual` >>
  drule_all abi_scratch_array_entry_metadata >> strip_tac >>
  `!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
    eval_operand op actual = SOME w` by
    (mp_tac (Q.INST [`infos` |-> `[]:(abi_enc_info # num # num # bool) list`,
       `dyn_ptr` |-> `parent_ptr`, `next` |-> `st.cs_next_var`, `site` |-> `st.cs_next_id`,
       `owner_next` |-> `allocated.cs_next_var`, `initial` |-> `initial:venom_state`,
       `prepared` |-> `prepared:venom_state`, `actual` |-> `actual:venom_state`]
       abi_scratch_prefix_operands) >>
     impl_tac >- (asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC) >> simp[]) >>
  `abi_decoder_operand_live allocated.cs_next_var parent_ptr` by
    (asm_simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     rpt strip_tac >> decide_tac) >>
  `abi_decoder_operand_live loop_st.cs_next_var parent_ptr` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `allocated.cs_next_var` >> simp[]) >>
  `first <= st.cs_next_id /\ st.cs_next_id < loop_st.cs_next_id` by
    (fs[abi_decoder_ids_def] >> decide_tac) >>
  drule_all abi_scratch_array_entry_cursor >> strip_tac >>
  drule_all abi_scratch_array_entry_frame >> disch_then assume_tac >>
  qexistsl_tac [`actual`, `slot`] >> gvs[] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> simp[]
QED

Theorem abi_scratch_array_entry_buffers:
  alloca_inv initial /\ abi_decoder_budget first last b cap initial /\ FINITE ids /\
  FLOOKUP initial.vs_allocas source_id = SOME (sb,source_cap) /\
  FLOOKUP initial.vs_allocas output_id = SOME (d,output_size) /\
  source_id <> output_id /\ 32 <= output_size /\ ~(source_id IN ids) /\ ~(output_id IN ids) ==>
  abi_footprint_disjoint sb source_cap (abi_decoder_child_scratch ids b cap initial) /\
  abi_footprint_disjoint d 32 (abi_decoder_child_scratch ids b cap initial) /\
  abi_footprint_disjoint sb source_cap [(d,32)] /\
  abi_footprint_disjoint d output_size (abi_decoder_child_scratch ids b cap initial) /\
  abi_footprint_disjoint sb source_cap [(d,output_size)] /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  sb + source_cap < dimword (:256) /\ d + output_size < dimword (:256)
Proof
  strip_tac >>
  `initial.vs_alloca_next <= b + cap /\ b + cap < dimword (:256)` by
    (fs[abi_decoder_budget_def] >> decide_tac) >>
  `sb + source_cap <= initial.vs_alloca_next` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `live` |-> `source_id`,
       `loff` |-> `sb`, `len` |-> `source_cap`, `p` |-> `sb`, `n` |-> `source_cap`]
       abi_caller_allocation_end) >> simp[]) >>
  `d + output_size <= initial.vs_alloca_next` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `live` |-> `output_id`,
       `loff` |-> `d:num`, `len` |-> `output_size`, `p` |-> `d:num`, `n` |-> `output_size`]
       abi_caller_allocation_end) >> simp[]) >>
  `abi_footprint_disjoint sb source_cap (abi_decoder_child_scratch ids b cap initial)` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `live` |-> `source_id`,
       `loff` |-> `sb`, `len` |-> `source_cap`, `p` |-> `sb`, `n` |-> `source_cap`]
       abi_caller_allocation_scratch) >> simp[]) >>
  `abi_footprint_disjoint d 32 (abi_decoder_child_scratch ids b cap initial)` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `live` |-> `output_id`,
       `loff` |-> `d:num`, `len` |-> `output_size`, `p` |-> `d:num`, `n` |-> `32`]
       abi_caller_allocation_scratch) >> simp[]) >>
  `abi_footprint_disjoint d output_size (abi_decoder_child_scratch ids b cap initial)` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `live` |-> `output_id`,
       `loff` |-> `d:num`, `len` |-> `output_size`, `p` |-> `d:num`, `n` |-> `output_size`]
       abi_caller_allocation_scratch) >> simp[]) >>
  `abi_footprint_disjoint sb source_cap [(d,output_size)]` by
    (drule_all abi_caller_allocation_separate >> simp[abi_footprint_disjoint_def]) >>
  drule_all abi_scratch_array_count_separate >> disch_then assume_tac >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_scratch_array_entry_caller:
  let cap = initial.vs_alloca_next + 32 * CARD (abi_decoder_missing first last initial) in
  abi_encode_array_prefix src dst st = (ops,loop_st) /\ fn_has_code st loop_st func /\
  alloca_inv initial /\ cap < dimword (:256) /\
  (!id off sz. id IN abi_decoder_ids first last /\
    FLOOKUP initial.vs_allocas id = SOME (off,sz) ==> sz = 32) /\
  abi_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    sb source_cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  st.cs_next_id IN abi_decoder_ids first last /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  FLOOKUP initial.vs_allocas source_id = SOME (sb,source_cap) /\
  FLOOKUP initial.vs_allocas output_id = SOME (d,output_size) /\
  source_id <> output_id /\ 32 <= output_size /\
  ~(source_id IN abi_decoder_ids first last) /\ ~(output_id IN abi_decoder_ids first last) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot.
    abi_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
      sb source_cap actual.vs_memory /\
    abi_footprint_disjoint sb source_cap
      (abi_decoder_child_scratch (abi_decoder_ids first last) 0 cap actual) /\
    abi_footprint_disjoint d output_size
      (abi_decoder_child_scratch (abi_decoder_ids first last) 0 cap actual) /\
    abi_footprint_disjoint sb source_cap [(d,output_size)] /\
    sb + source_cap < dimword (:256) /\ d + output_size < dimword (:256) /\
    abi_encoder_array_prefix ty avs 0 d actual.vs_memory /\
    abi_encoder_cursor T (FST ops) st.cs_next_id slot first st.cs_next_id loop_st 0 actual /\
    eval_operand (SND ops) actual = SOME (n2w (LENGTH avs)) /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_budget first last 0 cap actual /\
    abi_scratch_evolution (abi_decoder_ids first last) 0 cap initial actual /\
    abi_decode_footprint_frame
      ((d,32)::abi_decoder_child_scratch (abi_decoder_ids first last) 0 cap initial) initial actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = loop_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_caller_allocation_budget_zero >> strip_tac >>
  `FINITE (abi_decoder_ids first last)` by simp[] >>
  drule_all (Q.INST [`ids` |-> `abi_decoder_ids first last`]
    abi_scratch_array_entry_buffers) >> strip_tac >>
  drule_all (Q.INST [`ids` |-> `abi_decoder_ids first last`]
    abi_scratch_array_entry) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `abi_footprint_disjoint sb source_cap
    (abi_decoder_child_scratch (abi_decoder_ids first last) 0
      (initial.vs_alloca_next + 32 * CARD (abi_decoder_missing first last initial)) actual)` by
    (mp_tac (Q.INST [`ids` |-> `abi_decoder_ids first last`, `b` |-> `0:num`,
       `cap` |-> `initial.vs_alloca_next + 32 * CARD (abi_decoder_missing first last initial)`,
       `s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`,
       `p` |-> `sb`, `n` |-> `source_cap`] abi_scratch_disjoint_advance) >> simp[]) >>
  `abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) 0
      (initial.vs_alloca_next + 32 * CARD (abi_decoder_missing first last initial)) actual)` by
    (mp_tac (Q.INST [`ids` |-> `abi_decoder_ids first last`, `b` |-> `0:num`,
       `cap` |-> `initial.vs_alloca_next + 32 * CARD (abi_decoder_missing first last initial)`,
       `s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`,
       `p` |-> `d:num`, `n` |-> `output_size`] abi_scratch_disjoint_advance) >> simp[]) >>
  qexistsl_tac [`actual`, `slot`] >> simp[]
QED

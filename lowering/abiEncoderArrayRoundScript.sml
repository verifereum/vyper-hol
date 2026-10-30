Theory abiEncoderArrayRound
Ancestors
  abiEncoderArrayMemory abiEncoderArrayHeaderMemory abiEncoderArrayStaticIteration
  abiEncoderArrayDynamicMemory abiEncoderArrayBodyCode abiEncoderArrayCode abiEncoderArrayPrefix
  abiEncoderMembersDefs abiEncoderChildInputs abiEncoderAdmissible abiDecoderDynamicLoopSetup
  abiDecoderEffect abiDecoderContract abiDecoderReentry abiDecoderLoop fragExec compileEnv
  emitHelperProps emitHelper valueEncoding contractABI venomState finite_map words list
  arithmetic abiEncoderZeroCursorPrepare abiEncoderArrayParent abiDecoderIndexInit
  abiDecoderPrimitiveLoopFrames abiDecoderFrame abiEncoderArrayFrame abiEncoderChildEffect
  abiEncoderChildFrames abiDecoderExecution abiDecoderLoopRegisters abiDecoderArrayBackedge
  abiDecoderArrayInitExec abiDecoderAllocation abiDecoderProtectedScratch exprLoweringProps
  venomExecSemantics pred_set

(* Actual body execution retains the parent source and registered loop index. *)
Theorem abi_encode_array_addresses_index:
  abi_encode_array_addresses ip src dst asz msz st = (coords,prepared) ==>
  FST (FST coords) = Var (STRING #"%" (toString st.cs_next_var))
Proof
  simp[abi_encode_array_addresses_def, abi_decode_array_head_setup_def, abi_decode_indexed_coordinates_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem abi_encode_array_static_body_index:
  abi_encode_array_static_body ip src dst ei asz msz st = (out,end_st) ==>
  out = Var (STRING #"%" (toString st.cs_next_var))
Proof
  strip_tac >> drule abi_encode_array_static_body_trace >> strip_tac >>
  drule abi_encode_array_addresses_index >> asm_simp_tac bool_ss []
QED

Theorem abi_encode_array_dynamic_body_index:
  abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz st = (out,end_st) ==>
  out = Var (STRING #"%" (toString st.cs_next_var))
Proof
  strip_tac >> drule abi_encode_array_dynamic_body_trace >> strip_tac >>
  drule abi_encode_array_addresses_index >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_array_static_body_memory:
  abi_encoder_static_leaf ei /\ abi_encode_array_static_body ip src dst ei asz msz st = (out,end_st) /\
  fn_has_code st end_st func /\
  abi_encoder_array_memory ei asz msz F ty avs owner_st src dst sb source_cap d output_size b cap j initial /\
  abi_encoder_cursor T ip site slot first lo owner_st j initial /\ j < LENGTH avs /\
  owner_st.cs_next_var <= st.cs_next_var /\ owner_st.cs_next_id <= st.cs_next_id /\
  abi_decoder_budget first last b cap initial /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_encoder_array_memory ei asz msz F ty avs owner_st src dst sb source_cap
      d output_size b cap (SUC j) actual /\
    abi_encoder_cursor T ip site slot first lo owner_st j actual /\
    eval_operand out actual = SOME (n2w j) /\
    abi_decoder_effect first last st.cs_next_id end_st.cs_next_id owner_st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_array_memory _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_memory_def]) >>
  qpat_assum `abi_encoder_cursor T _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  drule_all abi_encode_array_static_body_context >> strip_tac >>
  `first <= st.cs_next_id /\ site < last /\ site < st.cs_next_id /\ owner_st.cs_next_id <= last` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `cursor_op` |-> `ip:operand`, `off` |-> `j:num`, `s` |-> `initial:venom_state`]
    abi_encoder_cursor_bounds) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_encoder_buffer_pre (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size b cap initial` by
    (irule abi_encoder_buffer_pre_mono >> qexists_tac `owner_st` >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`p` |-> `n2w slot:bytes32`] abi_encoder_array_static_iteration) >>
  impl_tac >- asm_simp_tac (srw_ss()) [w2n_n2w, Excl "enc_def"] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `abi_decoder_effect first last st.cs_next_id end_st.cs_next_id owner_st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`d`, `end_st.cs_next_id`, `st.cs_next_id`, `st.cs_next_var`, `output_size`] >> simp[]) >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `next` |-> `owner_st.cs_next_var`, `cursor_op` |-> `ip:operand`,
    `active` |-> `T`, `off` |-> `j:num`, `sz` |-> `output_size:num`, `owned_lo` |-> `st.cs_next_id`, `owned_hi` |-> `end_st.cs_next_id`]
    abi_encoder_cursor_effect_protected) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> disch_tac >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `dyn` |-> `F`, `k` |-> `SUC j`, `hi` |-> `end_st.cs_next_id`,
    `lo` |-> `st.cs_next_id`] abi_encoder_array_memory_advance) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

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

(* ===== Encoder Array Backedge ===== *)

(* Execute the shared ADD/MSTORE/JMP backedge and own its registered index slot.
   TOP-LEVEL: concrete execution and a reusable single-scratch-write effect. *)

Theorem abi_encoder_array_backedge_execute:
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString next)) ip hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w j) /\ eval_operand ip s = SOME (n2w slot) /\
  abi_decoder_operand_live next ip /\ slot < dimword (:256) /\
  j < n /\ n < dimword (:256) /\ next < limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. exec_block fuel ctx bb s = OK actual /\
    mload slot actual = n2w (SUC j) /\
    actual.vs_current_bb = hdr /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted /\
    fresh_vars_wrt limit_st actual /\
    (!op. abi_decoder_operand_live next op ==> eval_operand op actual = eval_operand op s) /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    abi_decode_footprint_frame [(slot,32)] s actual /\
    actual = jump_to hdr (mstore slot (n2w (SUC j))
      (update_var (STRING #"%" (toString next)) (n2w (SUC j)) s))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `ip <> Var (STRING #"%" (toString next))` by
    (mp_tac (Q.INST [`first` |-> `next:num`, `op` |-> `ip:operand`] abi_decoder_live_excludes_output) >>
     asm_simp_tac bool_ss [LESS_EQ_REFL]) >>
  qabbrev_tac `actual = jump_to hdr (mstore slot (n2w (SUC j))
    (update_var (STRING #"%" (toString next)) (n2w (SUC j)) s))` >>
  `exec_block fuel ctx bb s = OK actual` by
    (drule_all abi_decode_backedge_control >> simp[Abbr`actual`, w2n_n2w]) >>
  `abi_decode_footprint_frame [(slot,32)] s actual /\ mload slot actual = n2w (SUC j)` by
    (mp_tac (Q.INST [`p` |-> `n2w slot:bytes32`, `fp` |-> `[(slot:num,32:num)]`,
      `nv` |-> `STRING #"%" (toString (next:num))`, `w` |-> `n2w (SUC j):bytes32`]
      (INST_TYPE [alpha |-> ``:256``] abi_decode_backedge_observations)) >>
     simp[Abbr`actual`, w2n_n2w]) >>
  `fresh_vars_wrt limit_st actual` by
    simp[Abbr`actual`, abi_decoder_generated_update_fresh, fresh_vars_wrt_mstore] >>
  `!op. abi_decoder_operand_live next op ==> eval_operand op actual = eval_operand op s` by
    (rpt strip_tac >> asm_simp_tac bool_ss [Abbr`actual`, abi_decoder_operand_jump,
      abi_decoder_operand_mstore, abi_decoder_generated_update_operand]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  simp[Abbr`actual`, jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def]
QED

Theorem abi_encoder_array_backedge_reach:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString next)) ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w j) /\ eval_operand ip s = SOME (n2w slot) /\
  abi_decoder_operand_live next ip /\ slot < dimword (:256) /\
  j < n /\ n < dimword (:256) /\ next < limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. mload slot actual = n2w (SUC j) /\
    actual.vs_current_bb = hdr /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted /\
    fresh_vars_wrt limit_st actual /\
    (!op. abi_decoder_operand_live next op ==> eval_operand op actual = eval_operand op s) /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    abi_decode_footprint_frame [(slot,32)] s actual /\ abi_decode_sim ctx func s actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`fuel` |-> `0:num`] abi_encoder_array_backedge_execute) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `ip <> Var (STRING #"%" (toString next))` by
    (mp_tac (Q.INST [`first` |-> `next:num`, `op` |-> `ip:operand`] abi_decoder_live_excludes_output) >>
     asm_simp_tac bool_ss [LESS_EQ_REFL]) >>
  mp_tac (Q.INST [`fn` |-> `func`, `nv` |-> `STRING #"%" (toString (next:num))`,
    `p` |-> `n2w slot:bytes32`, `i` |-> `j:num`, `ncount` |-> `n:num`] abi_decode_backedge_sim) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  asm_simp_tac (srw_ss()) [w2n_n2w] >> disch_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_single_scratch_effect:
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < last /\
  lo <= site /\ site < hi /\ FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
  actual.vs_halted = initial.vs_halted /\ fresh_vars_wrt limit_st actual /\
  (!op. abi_decoder_operand_live next op ==> eval_operand op actual = eval_operand op initial) /\
  abi_decode_footprint_frame [(slot,32)] initial actual /\ (d+sz <= b \/ b+cap <= d) ==>
  abi_decoder_effect first last lo hi next limit_st d sz b cap initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `site IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  `abi_decode_footprint_frame [(d,sz);(slot,32)] initial actual` by
    (irule abi_encoder_frame_extra_window >> asm_simp_tac bool_ss []) >>
  drule_all abi_encoder_owned_scratch_frame >> disch_tac >>
  `abi_decoder_budget first last b cap actual` by
    (drule_all abi_decoder_budget_transport >> asm_simp_tac bool_ss []) >>
  `abi_decode_footprint_frame [(d,sz);(b,cap)] initial actual` by
    (irule abi_decode_footprint_frame_weaken >> qexists_tac `[(slot,32)]` >>
     asm_simp_tac (srw_ss()) [] >> qexistsl_tac [`b`, `cap`] >> asm_simp_tac (srw_ss()) []) >>
  asm_simp_tac bool_ss [abi_decoder_effect_def]
QED

(* ===== Memory ===== *)

(* The actual backedge advances the index and preserves the encoded prefix and tail cursor. *)

Theorem abi_encoder_array_backedge_memory:
  lookup_block initial.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString next)) ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  initial.vs_inst_idx = LENGTH prefix /\ ~initial.vs_halted /\
  eval_operand (Var iv) initial = SOME (n2w j) /\
  abi_encoder_array_memory ei asz msz active ty avs owner_st src dst sb source_cap d output_size b cap k initial /\
  abi_encoder_cursor T ip site slot first lo owner_st j initial /\
  abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first lo owner_st off initial /\
  (active ==> site < cursor_site) /\ owner_st.cs_next_id <= last /\
  owner_st.cs_next_var <= next /\ next < limit_st.cs_next_var /\
  j < LENGTH avs /\ fresh_vars_wrt limit_st initial /\ abi_decoder_budget first last b cap initial ==>
  ?actual. abi_encoder_array_memory ei asz msz active ty avs owner_st src dst sb source_cap
      d output_size b cap k actual /\
    abi_encoder_cursor T ip site slot first lo owner_st (SUC j) actual /\
    abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first lo owner_st off actual /\
    abi_decoder_effect first last site (site+1) owner_st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = hdr /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_array_memory_typed >> strip_tac >>
  qpat_assum `abi_encoder_cursor T ip _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `s` |-> `initial:venom_state`,
    `cursor_op` |-> `ip:operand`, `off` |-> `j:num`] abi_encoder_cursor_bounds) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_decoder_operand_live next ip` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `owner_st.cs_next_var` >> simp[]) >>
  qpat_assum `abi_encoder_array_memory _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_encoder_array_memory_def]) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `n` |-> `LENGTH (avs:abi_value list)`]
    abi_encoder_array_backedge_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  mp_tac (Q.INST [`lo` |-> `site:num`, `hi` |-> `site+1`, `sz` |-> `output_size:num`]
    abi_encoder_single_scratch_effect) >>
  impl_tac >- asm_simp_tac (srw_ss()) [Excl "enc_def"] >> disch_tac >>
  `abi_decoder_effect first last site (site+1) owner_st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_decoder_effect_widen >> qexistsl_tac [`d`, `site+1`, `site`, `next`, `output_size`] >> simp[]) >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `new_j` |-> `SUC j`] abi_encoder_array_index_update) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

(* One actual static-element body and its emitted backedge form a complete loop round. *)
Theorem abi_encoder_array_static_round:
  abi_encoder_static_leaf ei /\ abi_encode_array_static_body ip src dst ei asz msz st = (out,end_st) /\
  fn_has_code st end_st func /\
  lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = end_st.cs_current_insts ++ abi_decode_backedge_insts end_st.cs_next_id
    (STRING #"%" (toString st.cs_next_var)) (STRING #"%" (toString end_st.cs_next_var)) ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  abi_encoder_array_memory ei asz msz F ty avs owner_st src dst sb source_cap d output_size b cap j initial /\
  abi_encoder_cursor T ip site slot first lo owner_st j initial /\ j < LENGTH avs /\
  owner_st.cs_next_var <= st.cs_next_var /\ owner_st.cs_next_id <= st.cs_next_id /\
  abi_decoder_budget first last b cap initial /\ end_st.cs_next_id+3 <= last /\
  end_st.cs_next_var+1 <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_encoder_array_memory ei asz msz F ty avs owner_st src dst sb source_cap
      d output_size b cap (SUC j) actual /\
    abi_encoder_cursor T ip site slot first lo owner_st (SUC j) actual /\
    abi_decoder_effect first last site (end_st.cs_next_id+3) owner_st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = hdr /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_static_body_context >> strip_tac >>
  drule abi_encode_array_static_body_index >> disch_tac >>
  qpat_assum `abi_encoder_cursor T ip _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  `owner_st.cs_next_id <= last /\ end_st.cs_next_id <= last /\
    end_st.cs_next_var <= limit_st.cs_next_var /\ end_st.cs_next_var < limit_st.cs_next_var /\
    owner_st.cs_next_var <= end_st.cs_next_var /\ site < st.cs_next_id` by decide_tac >>
  mp_tac abi_encoder_array_static_body_memory >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial encoded` >>
  qpat_assum `out = Var _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qpat_assum `abi_decoder_effect _ _ st.cs_next_id end_st.cs_next_id _ _ _ _ _ _ initial encoded`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_effect_def]) >>
  mp_tac (Q.INST [`initial` |-> `encoded:venom_state`, `active` |-> `F`, `k` |-> `SUC j`,
    `dyn_ptr` |-> `Lit 0w`, `cursor_site` |-> `0:num`, `cursor_slot` |-> `0:num`, `off` |-> `0:num`,
    `prefix` |-> `end_st.cs_current_insts`, `id` |-> `end_st.cs_next_id`, `next` |-> `end_st.cs_next_var`,
    `iv` |-> `STRING #"%" (toString st.cs_next_var)`] abi_encoder_array_backedge_memory) >>
  impl_tac >- full_simp_tac bool_ss [abi_encoder_cursor_def] >> strip_tac >>
  rename1 `abi_decode_sim ctx func encoded actual` >>
  `abi_decoder_effect first last site (end_st.cs_next_id+3) owner_st.cs_next_var
    limit_st d output_size b cap initial encoded` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`d`, `end_st.cs_next_id`, `st.cs_next_id`, `owner_st.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_decoder_effect first last site (end_st.cs_next_id+3) owner_st.cs_next_var
    limit_st d output_size b cap encoded actual` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`d`, `site+1`, `site`, `owner_st.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_decoder_effect first last site (end_st.cs_next_id+3) owner_st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_decoder_effect_trans >> qexists_tac `encoded` >> asm_simp_tac bool_ss []) >>
  `abi_decode_sim ctx func initial actual` by
    (irule abi_decode_sim_trans >> qexists_tac `encoded` >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

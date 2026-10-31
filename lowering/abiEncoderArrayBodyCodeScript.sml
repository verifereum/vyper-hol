Theory abiEncoderArrayBodyCode
Ancestors
  abiEncoderInput abiCanonicalWindows abiCanonicalHeadSize abiDecodeRanges valueEncoding
  contractABI words list rich_list arithmetic abiEncoderArrayCode abiDecoderDynamicLoopSetup
  abiDecoderReentryAddress abiDecoderReentry abiDecoderGuards abiDecoderContract
  abiDecoderArrayHeader emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomState venomInst abiDecoderLoop fragExec instIdxIndep
  abiEncoderChildInputs abiDecoderArraySlice abiEncoderAdmissible abiEncoderLeafCode
  abiEncoderChildContext abiEncoderAppend abiEncoderCounters abiEncoder

(* Uniform semantic layout and complete source slots for dynamic-array encoding. *)
Theorem abi_encoder_have_type_every:
  !vs ty. have_type ty vs = EVERY (has_type ty) vs
Proof
  Induct >> simp_tac bool_ss [has_type_def, EVERY_DEF] >> rpt gen_tac >> simp[]
QED

Theorem abi_encoder_array_prefix_types:
  has_type (Array NONE ty) (ListV avs) /\ j <= LENGTH avs ==>
  has_types (REPLICATE j ty) (TAKE j avs) /\ LENGTH (TAKE j avs) = j /\ LENGTH avs < dimword (:256)
Proof
  simp_tac (srw_ss()) [Once has_type_def, valid_length_def, LET_THM, abi_encoder_have_type_every] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH (TAKE j avs) = j` by simp[] >> asm_simp_tac bool_ss [] >>
  `has_types (REPLICATE (LENGTH (TAKE j avs)) ty) (TAKE j avs)` by
    simp[GSYM have_type_has_types_REPLICATE, abi_encoder_have_type_every, EVERY_TAKE] >>
  qpat_assum `LENGTH (TAKE j avs) = j`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th, LET_THM]) >> PURE_REWRITE_TAC [th, LET_THM]) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_encoder_uniform_sizes:
  !vs ty. SUM (MAP abi_member_head_size (REPLICATE (LENGTH vs) ty)) =
    LENGTH vs * abi_member_head_size ty /\
    MAP2 abi_member_tail_size (REPLICATE (LENGTH vs) ty) vs =
    MAP (abi_member_tail_size ty) vs
Proof
  Induct >> simp[REPLICATE, MULT_CLAUSES]
QED

Theorem abi_encoder_array_prefix_sizes:
  has_type (Array NONE ty) (ListV avs) /\ j <= LENGTH avs ==>
  LENGTH (FLAT (abi_tuple_heads hl 0 (REPLICATE j ty) (TAKE j avs))) =
    j * abi_member_head_size ty /\
  LENGTH (FLAT (abi_tuple_tails (REPLICATE j ty) (TAKE j avs))) =
    SUM (MAP (abi_member_tail_size ty) (TAKE j avs))
Proof
  strip_tac >> drule_all abi_encoder_array_prefix_types >> strip_tac >>
  mp_tac (Q.SPECL [`TAKE j avs`, `ty`] abi_encoder_uniform_sizes) >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  asm_simp_tac (srw_ss()) [abi_tuple_heads_length, abi_tuple_tails_length]
QED

Theorem abi_encoder_array_selected_input:
  abi_encoder_input (AbiDynArray ei asz msz dyn) (Array NONE ty) (ListV avs) sb capacity mem /\
  j < LENGTH avs ==>
  abi_encoder_input ei ty (EL j avs) (sb+32+j*msz) msz mem /\
  has_type ty (EL j avs) /\ asz = abi_member_head_size ty /\ dyn = is_dynamic ty /\
  32+j*msz+msz <= capacity
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_encoder_input _ _ _ _ _ _`
    (qx_choose_then `ct` (qx_choose_then `values` (MAP_EVERY assume_tac o CONJUNCTS)) o
      REWRITE_RULE [abi_encoder_array_input_iff]) >>
  gvs[] >> rename1 `has_types (REPLICATE (LENGTH avs) ty) avs` >>
  `abi_encoder_input ei ty (EL j avs) (sb+32+j*msz) msz mem` by simp[] >>
  drule abi_encoder_input_typed >> strip_tac >>
  mp_tac (Q.INST [`i` |-> `j:num`, `ncount` |-> `LENGTH (avs:abi_value list)`,
    `cap` |-> `capacity:num`, `mem_sz` |-> `msz:num`] abi_encoder_array_slot_bound) >>
  impl_tac >- (full_simp_tac bool_ss [AC ADD_COMM ADD_ASSOC, MULT_COMM]) >>
  asm_simp_tac (srw_ss()) [AC ADD_COMM ADD_ASSOC]
QED

Theorem abi_encoder_array_encoding_bound:
  has_type (Array NONE ty) (ListV avs) ==>
  32+LENGTH avs*abi_member_head_size ty <= LENGTH (enc (Array NONE ty) (ListV avs))
Proof
  strip_tac >> drule canonical_array_length >> simp[]
QED

Theorem abi_encoder_array_static_size:
  has_type (Array NONE ty) (ListV avs) /\ ~is_dynamic ty ==>
  LENGTH (enc (Array NONE ty) (ListV avs)) = 32+LENGTH avs*abi_member_head_size ty
Proof
  strip_tac >> drule canonical_array_length >>
  `SUM (MAP (abi_member_tail_size ty) avs) = 0` by
    (Induct_on `avs` >> simp[abi_member_tail_size_def]) >> simp[]
QED

(* ===== Encoder Array Address ===== *)

(* Execute the shared seven-instruction encoder body address prefix. *)

Theorem abi_encode_array_addresses_shape:
  abi_encode_array_addresses ip src dst asz msz st = (coords,st') ==>
  st'.cs_next_var = st.cs_next_var+7 /\ st'.cs_next_id = st.cs_next_id+7 /\
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\ inst_extends st st' /\
  abi_decoder_operand_live st'.cs_next_var (FST (FST coords)) /\
  abi_decoder_operand_live st'.cs_next_var (SND (FST coords)) /\
  abi_decoder_operand_live st'.cs_next_var (FST (SND coords)) /\
  abi_decoder_operand_live st'.cs_next_var (SND (SND coords)) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')
Proof
  simp[abi_encode_array_addresses_def, abi_decode_array_head_setup_def, abi_decode_indexed_coordinates_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND, abi_decoder_operand_live_def,
    abi_decoder_older_vars_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def] >>
  rpt strip_tac >> decide_tac
QED

Theorem abi_encode_array_addresses_sequence:
  abi_encode_array_addresses ip src dst asz msz st = (coords,st') /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    eval_operand (FST (FST coords)) actual = SOME (n2w j) /\
    eval_operand (SND (FST coords)) actual = SOME (n2w (sb+32+j*msz)) /\
    eval_operand (FST (SND coords)) actual = SOME (n2w (d+32)) /\
    eval_operand (SND (SND coords)) actual = SOME (n2w (d+32+j*asz)) /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_address_frame st.cs_next_var initial actual /\
    inst_extends st st'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encode_array_addresses_trace >> strip_tac >>
  drule abi_decode_array_head_setup_counters >> strip_tac >>
  drule abi_decode_indexed_coordinates_counters >> strip_tac >>
  `middle.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= middle.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `st'` |-> `middle`, `ops` |-> `src_ops`,
    `abi_sz` |-> `msz:num`, `i` |-> `j:num`] abi_decode_array_head_setup_reentry) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st middle) initial = OK ready` >>
  `eval_operand dst ready = SOME (n2w d)` by
    (fs[abi_decoder_address_frame_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`st` |-> `middle`, `base_op` |-> `dst`, `idx` |-> `FST (src_ops:operand # operand # operand)`,
    `stride` |-> `asz:num`, `s` |-> `ready:venom_state`, `i` |-> `j:num`,
    `sb` |-> `d:num`, `ops` |-> `dst_ops`] abi_decode_indexed_coordinates_reentry) >>
  impl_tac >- full_simp_tac bool_ss [] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts middle st') ready = OK actual` >>
  `eval_operand (FST src_ops) actual = SOME (n2w j) /\
    eval_operand (SND (SND src_ops)) actual = SOME (n2w (sb+32+j*msz))` by
    (fs[abi_decoder_address_frame_def] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts st st') initial = OK actual /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`ready`, `middle`] >> simp[]) >>
  `abi_decoder_address_frame st.cs_next_var initial actual` by
    (irule abi_decoder_address_frame_trans >> qexistsl_tac [`middle.cs_next_var`, `ready`] >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) []
QED

(* ===== Reach ===== *)

(* The shared encoder body address prefix reaches its real instruction endpoint. *)

Theorem abi_encode_array_addresses_from_state:
  abi_encode_array_addresses ip src dst asz msz st = (coords,st') /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\t. eval_operand (FST (FST coords)) t = SOME (n2w j) /\
      eval_operand (SND (FST coords)) t = SOME (n2w (sb+32+j*msz)) /\
      eval_operand (FST (SND coords)) t = SOME (n2w (d+32)) /\
      eval_operand (SND (SND coords)) t = SOME (n2w (d+32+j*asz)) /\
      fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t) (K F)
Proof
  strip_tac >> drule abi_encode_array_addresses_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by fs[inst_extends_def, IS_PREFIX_APPEND] >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_encode_array_addresses_sequence >> strip_tac >> qexists_tac `actual` >>
  gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx]
QED

Theorem abi_encode_array_addresses_reach:
  abi_encode_array_addresses ip src dst asz msz st = (coords,st') /\ fn_has_code st st' func /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. eval_operand (FST (FST coords)) t = SOME (n2w j) /\
    eval_operand (SND (FST coords)) t = SOME (n2w (sb+32+j*msz)) /\
    eval_operand (FST (SND coords)) t = SOME (n2w (d+32)) /\
    eval_operand (SND (SND coords)) t = SOME (n2w (d+32+j*asz)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t /\
    t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_addresses_from_state >> disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `~actual.vs_halted` by fs[abi_decoder_address_frame_def] >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

(* Complete parent source data establishes the selected child's real buffer input. *)
Theorem abi_encoder_array_child_buffer:
  abi_encoder_buffer_pre (AbiDynArray ei asz msz dyn) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size b cap initial /\
  j < LENGTH avs /\ LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\
  abi_decoder_address_frame st.cs_next_var initial actual /\
  abi_decoder_operand_live prepared.cs_next_var child_src /\
  abi_decoder_operand_live prepared.cs_next_var data_op /\
  eval_operand child_src actual = SOME (n2w (sb+32+j*msz)) /\
  eval_operand data_op actual = SOME (n2w (d+32)) ==>
  abi_encoder_buffer_pre ei ty (EL j avs) prepared child_src data_op
    (sb+32+j*msz) msz (d+32) (output_size-32) b cap actual /\
  asz = abi_member_head_size ty /\ dyn = is_dynamic ty
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  drule_all abi_encoder_array_selected_input >> strip_tac >>
  qpat_assum `abi_encoder_input (AbiDynArray _ _ _ _) _ _ _ _ _`
    (assume_tac o MATCH_MP abi_encoder_input_typed) >>
  drule abi_encoder_array_encoding_bound >> strip_tac >>
  `32 <= output_size /\ d+32+(output_size-32) = d+output_size` by decide_tac >>
  `actual.vs_memory = initial.vs_memory` by fs[abi_decoder_address_frame_def] >>
  asm_simp_tac bool_ss [abi_encoder_buffer_pre_def] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [ADD_ASSOC]) >> PURE_REWRITE_TAC [ADD_ASSOC] >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_encoder_array_prepare:
  abi_encode_array_addresses ip src dst asz msz st = (coords,prepared) /\
  fn_has_code st prepared func /\
  abi_encoder_buffer_pre (AbiDynArray ei asz msz dyn) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size b cap initial /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\ j < LENGTH avs /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready. abi_encoder_buffer_pre ei ty (EL j avs) prepared
      (SND (FST coords)) (FST (SND coords)) (sb+32+j*msz) msz (d+32) (output_size-32) b cap ready /\
    asz = abi_member_head_size ty /\ dyn = is_dynamic ty /\
    eval_operand (FST (FST coords)) ready = SOME (n2w j) /\
    eval_operand (SND (SND coords)) ready = SOME (n2w (d+32+j*asz)) /\
    fresh_vars_wrt limit_st ready /\ abi_decoder_address_frame st.cs_next_var initial ready /\
    ready.vs_current_bb = prepared.cs_current_bb /\ ready.vs_inst_idx = LENGTH prepared.cs_current_insts /\
    ~ready.vs_halted /\ abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  drule abi_encode_array_addresses_shape >> strip_tac >>
  mp_tac (Q.INST [`st'` |-> `prepared`] abi_encode_array_addresses_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  mp_tac (Q.INST [`actual` |-> `ready:venom_state`,
    `child_src` |-> `SND (FST (coords:(operand # operand) # (operand # operand)))`,
    `data_op` |-> `FST (SND (coords:(operand # operand) # (operand # operand)))`]
    abi_encoder_array_child_buffer) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `ready` >> asm_simp_tac bool_ss []
QED

(* The next encoded child fits between the array's head and tail frontiers. *)
Theorem abi_encoder_array_child_bounds:
  has_type (Array NONE ty) (ListV avs) /\ j < LENGTH avs /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size ==>
  32 <= output_size /\ has_type ty (EL j avs) /\
  j*abi_member_head_size ty+abi_member_head_size ty <= LENGTH avs*abi_member_head_size ty /\
  LENGTH avs*abi_member_head_size ty+
    SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) <= output_size-32 /\
  (is_dynamic ty ==>
    j*abi_member_head_size ty+32 <= LENGTH avs*abi_member_head_size ty /\
    LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs))+
      LENGTH (enc ty (EL j avs)) <= output_size-32) /\
  (~is_dynamic ty ==>
    j*abi_member_head_size ty+LENGTH (enc ty (EL j avs)) <= LENGTH avs*abi_member_head_size ty)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `TAKE j avs++EL j avs::DROP (SUC j) avs = avs` by
    (mp_tac (Q.ISPEC `avs:abi_value list` (Q.SPEC `j:num` TAKE_DROP_SUC)) >>
     asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
  `LENGTH (TAKE j avs) = j` by simp[] >>
  qpat_assum `has_type (Array NONE ty) (ListV avs)`
    (assume_tac o SIMP_RULE (srw_ss()) [Once has_type_def, abi_encoder_have_type_every]) >>
  `has_type ty (EL j avs)` by fs[EVERY_EL] >>
  mp_tac (Q.SPECL [`j:num`, `LENGTH (avs:abi_value list)`, `abi_member_head_size ty`]
    abi_decoder_array_cell_capacity) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  drule canonical_array_length >> strip_tac >>
  `SUM (MAP (abi_member_tail_size ty) avs) =
    SUM (MAP (abi_member_tail_size ty) (TAKE j avs))+abi_member_tail_size ty (EL j avs)+
      SUM (MAP (abi_member_tail_size ty) (DROP (SUC j) avs))` by
    (qpat_assum `TAKE j avs++_ = avs`
      (mp_tac o AP_TERM ``\xs. SUM (MAP (abi_member_tail_size ty) xs)``) >>
     simp_tac bool_ss [MAP_APPEND, SUM_APPEND, MAP, SUM] >> decide_tac) >>
  mp_tac (Q.INST [`bound` |-> `NONE:num option`, `pre` |-> `TAKE j (avs:abi_value list)`,
    `v` |-> `EL j (avs:abi_value list)`, `post` |-> `DROP (SUC j) (avs:abi_value list)`]
    canonical_array_member_ranges) >>
  impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss [LET_THM] >> strip_tac >>
  `~is_dynamic ty ==> LENGTH (enc ty (EL j avs)) = abi_member_head_size ty` by
    (strip_tac >> drule_all (cj 1 enc_has_static_length) >> simp[abi_member_head_size_def]) >>
  asm_simp_tac bool_ss [] >> Cases_on `is_dynamic ty` >>
  full_simp_tac (srw_ss()) [abi_member_head_size_def, Excl "enc_def"] >> decide_tac
QED

(* Extract actual body phases and their containing-function code. *)
Theorem abi_encode_array_static_body_trace:
  abi_encode_array_static_body ip src dst ei asz msz st = (out,end_st) ==>
  ?coords prepared ignored.
    abi_encode_array_addresses ip src dst asz msz st = (coords,prepared) /\
    compile_abi_encode_static_info (SND (SND coords)) (SND (FST coords)) ei prepared = (ignored,end_st) /\
    out = FST (FST coords)
Proof
  simp_tac bool_ss [abi_encode_array_static_body_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `abi_encode_array_addresses _ _ _ _ _ st = (coords,prepared)` >>
  rename1 `compile_abi_encode_static_info _ _ ei prepared = (ignored,end_st)` >>
  qexistsl_tac [`coords`, `prepared`, `ignored`] >> asm_simp_tac bool_ss []
QED

Theorem abi_encode_array_static_body_context:
  abi_encoder_static_leaf ei /\ abi_encode_array_static_body ip src dst ei asz msz st = (out,end_st) /\
  fn_has_code st end_st func ==>
  ?coords prepared ignored.
    abi_encode_array_addresses ip src dst asz msz st = (coords,prepared) /\
    compile_abi_encode_static_info (SND (SND coords)) (SND (FST coords)) ei prepared = (ignored,end_st) /\
    out = FST (FST coords) /\ fn_has_code st prepared func /\ fn_has_code prepared end_st func /\
    prepared.cs_next_id = st.cs_next_id+7 /\ prepared.cs_next_var = st.cs_next_var+7 /\
    prepared.cs_next_id <= end_st.cs_next_id /\ prepared.cs_next_var <= end_st.cs_next_var /\
    prepared.cs_blocks = st.cs_blocks /\ end_st.cs_blocks = prepared.cs_blocks
Proof
  strip_tac >> drule abi_encode_array_static_body_trace >> strip_tac >>
  drule abi_encode_array_addresses_shape >> strip_tac >>
  qpat_assum `abi_encoder_static_leaf ei` (fn th =>
    qpat_assum `compile_abi_encode_static_info _ _ _ _ = _`
      (assume_tac o PURE_REWRITE_RULE [MATCH_MP abi_encode_static_info_agrees th])) >>
  drule_all abi_encode_static_leaf_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >> drule cs_extends_abi_encode >> strip_tac >>
  `cs_extends st prepared` by (irule abi_encoder_straight_extends >> asm_simp_tac bool_ss []) >>
  drule_all fn_has_code_split >> strip_tac >>
  qexistsl_tac [`coords`, `prepared`, `ignored`] >> asm_simp_tac bool_ss []
QED

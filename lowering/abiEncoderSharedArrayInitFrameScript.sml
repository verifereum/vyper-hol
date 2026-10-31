Theory abiEncoderSharedArrayInitFrame
Ancestors
  abiEncoderSharedContract abiEncoderOpenInput abiEncoderOpenInputFrame abiEncoderArrayFrame
  abiEncoderArrayBodyCode abiEncoderInput abiDecoderFootprint abiDecoderContract
  abiDecoderReentry abiCanonicalWindows abiDecodeRanges abiCanonicalHeadSize
  abiEncoderSharedMembersCorrect abiEncoderArrayPrefix abiEncoderTuple abiEncoderMemory
  valueEncoding contractABI venomState venomMemDefs list rich_list arithmetic words
  abiEncoderArrayParent abiDecoderArrayHeader abiDecoderArrayLoopInit abiDecoderGuards
  abiEncoderMemberPhaseRaw abiEncoderMemberPhaseEffect abiEncoderRegisteredEffect
  abiEncoderExtendSim abiScratchLeafEffect abiScratchEffect abiDecoderAllocation abiDecoderFrame
  abiDecoderFrameCompose abiDecoderDynamicLoopSetup exprLoweringProps compileEnv emitHelper
  emitHelperProps venomInst venomExecSemantics instIdxIndep valueEncodingProps abiScratchSubset
  pred_set

(* Open array windows: no aggregate has_type/cardinality restriction is introduced. *)
Theorem abi_encoder_open_array_iff:
  abi_encoder_open_input (AbiDynArray ei asz msz active) at av sb source_cap mem <=>
  ?ty avs. at = Array NONE ty /\ av = ListV avs /\ valid_length NONE avs /\
    asz = abi_member_head_size ty /\ active = is_dynamic ty /\
    32+LENGTH avs*msz <= source_cap /\ mem_word_at sb mem = n2w (LENGTH avs) /\
    (!i. i < LENGTH avs ==>
      abi_encoder_open_input ei ty (EL i avs) (sb+32+i*msz) msz mem)
Proof
  simp[Once abi_encoder_open_input_cases] >> metis_tac[]
QED

Theorem abi_encoder_shared_array_input_facts:
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (st,src,dst) (sb,source_cap) (d,output_size) (first,last,b,cap) s ==>
  valid_length NONE avs /\ LENGTH avs < dimword (:256) /\
  asz = abi_member_head_size ty /\ active = is_dynamic ty /\
  32+LENGTH avs*msz <= source_cap /\
  mem_word_at sb s.vs_memory = n2w (LENGTH avs) /\
  (!i. i < LENGTH avs ==>
    abi_encoder_open_input ei ty (EL i avs) (sb+32+i*msz) msz s.vs_memory) /\
  LIST_REL abi_encoder_structural_valid (REPLICATE (LENGTH avs) ty) avs
Proof
  simp_tac bool_ss [abi_encoder_shared_input_def, abi_encoder_open_array_iff] >>
  strip_tac >> gvs[Excl "enc_def"] >>
  asm_simp_tac (srw_ss()) [valid_length_def, LIST_REL_EL_EQN, EL_REPLICATE] >>
  metis_tac[abi_encoder_open_input_valid]
QED

Theorem abi_encoder_shared_array_selected_input:
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (st,src,dst) (sb,source_cap) (d,output_size) (first,last,b,cap) s /\
  j < LENGTH avs /\ LENGTH (enc ty (EL j avs)) <= output_size /\
  eval_operand child_src s = SOME (n2w (sb+32+j*msz)) /\
  abi_decoder_operand_live st.cs_next_var child_src ==>
  abi_encoder_shared_input (ei,ty,EL j avs) (st,child_src,dst)
    (sb+32+j*msz,msz) (d,output_size) (first,last,b,cap) s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_shared_array_input_facts >> strip_tac >>
  qpat_assum `abi_encoder_shared_input _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_input_def]) >>
  `sb+32+j*msz+msz <= sb+source_cap` by
    (`SUC j*msz <= LENGTH avs*msz` by simp[] >>
     pop_assum mp_tac >> pure_rewrite_tac[MULT_CLAUSES] >>
     simp_tac bool_ss [MULT_COMM] >> decide_tac) >>
  `regions_disjoint (sb+32+j*msz,msz) (d,output_size)` by
    (gvs[abi_encoder_zero_aware_separation] >> decide_tac) >>
  `abi_footprint_disjoint (sb+32+j*msz) msz
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (irule abi_footprint_disjoint_subwindow >> qexistsl_tac [`sb`,`source_cap`] >> simp[] >> decide_tac) >>
  asm_simp_tac bool_ss [abi_encoder_shared_input_def] >> decide_tac
QED

Theorem abi_encoder_open_array_length:
  LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) ty) avs ==>
  LENGTH (enc (Array NONE ty) (ListV avs)) =
    32 + LENGTH avs*abi_member_head_size ty + SUM (MAP (abi_member_tail_size ty) avs)
Proof
  strip_tac >> simp_tac bool_ss [canonical_array_tuple, LENGTH_APPEND, LENGTH_enc_number] >>
  drule abi_encoder_open_tuple_length >> simp[uniform_member_sizes]
QED

Theorem abi_encoder_open_array_prefix_complete:
  LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) ty) avs /\
  abi_encoder_array_prefix ty avs (LENGTH avs) d mem ==>
  mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) mem =
    enc (Array NONE ty) (ListV avs)
Proof
  strip_tac >>
  `head_lengths (REPLICATE (LENGTH avs) ty) 0 = LENGTH avs*abi_member_head_size ty` by
    simp[head_lengths_acc, uniform_member_sizes] >>
  qpat_assum `abi_encoder_array_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE (srw_ss()) [abi_encoder_array_prefix_def]) >>
  `mem_bytes_at (d+32) (LENGTH (enc (Tuple (REPLICATE (LENGTH avs) ty)) (ListV avs))) mem =
    enc (Tuple (REPLICATE (LENGTH avs) ty)) (ListV avs)` by
    (irule abi_encoder_open_tuple_prefix_complete >> simp[]) >>
  `mem_bytes_at d (LENGTH (enc_number (Uint 256) (NumV (LENGTH avs)))) mem =
    enc_number (Uint 256) (NumV (LENGTH avs))` by
    simp[abi_encoder_word_window, enc_number_def] >>
  simp_tac bool_ss [canonical_array_tuple] >>
  irule abi_encoder_memory_append >> asm_simp_tac (srw_ss()) [LENGTH_enc_number, Excl "enc_def"]
QED

Theorem abi_encoder_open_array_prefix_output_frame:
  LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) ty) avs /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_decode_footprint_frame fp initial actual /\ abi_footprint_disjoint d output_size fp ==>
  abi_encoder_array_prefix ty avs j d actual.vs_memory
Proof
  strip_tac >>
  `j <= LENGTH avs` by fs[abi_encoder_array_prefix_def] >>
  `LIST_REL abi_encoder_layout_valid (REPLICATE j ty) (TAKE j avs)` by
    (gvs[LIST_REL_EL_EQN, LENGTH_TAKE, EL_REPLICATE, EL_TAKE] >> metis_tac[]) >>
  `LENGTH (FLAT (abi_tuple_heads (LENGTH avs*abi_member_head_size ty) 0 (REPLICATE j ty) (TAKE j avs))) =
     j*abi_member_head_size ty` by
    (simp[abi_encoder_open_heads_length] >>
     mp_tac (Q.SPECL [`TAKE j avs`,`ty`] abi_encoder_uniform_sizes) >> simp[]) >>
  `LENGTH (FLAT (abi_tuple_tails (REPLICATE j ty) (TAKE j avs))) =
     SUM (MAP (abi_member_tail_size ty) (TAKE j avs))` by
    (simp[abi_tuple_tails_length] >>
     mp_tac (Q.SPECL [`TAKE j avs`,`ty`] abi_encoder_uniform_sizes) >> simp[]) >>
  `SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) <=
     SUM (MAP (abi_member_tail_size ty) avs)` by
    (Cases_on `j = LENGTH avs` >- simp[] >>
     mp_tac (Q.ISPECL [`abi_member_tail_size ty`,`avs:abi_value list`,`j:num`]
       abi_encoder_prefix_sum_bound) >>
     impl_tac >- decide_tac >> decide_tac) >>
  `j*abi_member_head_size ty <= LENGTH avs*abi_member_head_size ty` by simp[] >>
  drule abi_encoder_open_array_length >> disch_tac >>
  full_simp_tac bool_ss [] >>
  irule abi_encoder_array_prefix_frame >> qexistsl_tac [`fp`,`initial`] >>
  asm_simp_tac bool_ss [] >> rpt conj_tac >>
  irule abi_footprint_disjoint_subwindow >> qexistsl_tac [`d`,`output_size`] >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

(* Count-copy observations at the one supplied concrete raw endpoint. *)
Theorem abi_encoder_array_count_raw_transport:
  abi_decode_array_header dst src MLOAD st = (cnt,final) /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var dst /\ sb < dimword (:256) /\ d < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready ==>
  eval_operand cnt ready = SOME (mload sb initial) /\
  mem_word_at d ready.vs_memory = mload sb initial /\
  fresh_vars_wrt limit_st ready /\ abi_decode_frame d 32 initial ready /\
  ready.vs_allocas = initial.vs_allocas /\ ready.vs_alloca_next = initial.vs_alloca_next /\
  ready.vs_halted = initial.vs_halted /\
  (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
    eval_operand op ready = SOME w)
Proof
  strip_tac >> drule_all abi_encoder_array_count_copy_sequence >> strip_tac >>
  gvs[abi_encoder_member_phase_raw_def, eval_op_inst_idx, fresh_vars_wrt_def,
    abi_decode_frame_def] >> metis_tac[]
QED

Theorem abi_encoder_array_count_opcodes:
  abi_decode_array_header dst src MLOAD st = (cnt,final) ==>
  EVERY (\i. i.inst_opcode = ADD \/ i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE)
    (emitted_insts st final)
Proof
  simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_encoder_array_count_registered:
  abi_decode_array_header dst src MLOAD st = (cnt,final) /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var dst /\ sb < dimword (:256) /\ d < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready /\ 32 <= sz ==>
  abi_encoder_registered_effect ids [(d,sz)] initial ready /\
  (alloca_inv initial ==> alloca_inv ready)
Proof
  strip_tac >> drule_all abi_encoder_array_count_raw_transport >> strip_tac >>
  `ready.vs_accounts = initial.vs_accounts /\ ready.vs_transient = initial.vs_transient /\
   ready.vs_logs = initial.vs_logs /\ ready.vs_requests = initial.vs_requests` by
    (irule abi_encoder_member_phase_globals >> goal_assum (drule_at Any) >>
     drule abi_encoder_array_count_opcodes >> simp[]) >>
  conj_tac
  >- (simp_tac bool_ss [abi_encoder_registered_effect_def] >>
      gvs[abi_decode_frame_def] >> rpt strip_tac >>
      first_x_assum irule >> fs[] >> decide_tac) >>
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED

Theorem abi_encoder_array_count_extend:
  abi_decode_array_header dst src MLOAD st = (cnt,final) /\ fn_has_code st final func /\
  abi_encoder_member_phase_raw st final initial ready /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_extend_sim ctx func initial ready
Proof
  strip_tac >>
  drule (Q.INST [`opc` |-> `MLOAD`] abi_decode_array_header_shape) >>
  simp[abi_decode_source_opcode_def, EVERY_CONJ] >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st final)` by
    fs[EVERY_CONJ] >>
  drule_all abi_encoder_member_phase_extend_sim >> simp[]
QED

Theorem abi_encoder_shared_array_count_effect:
  abi_decode_array_header dst src MLOAD st = (cnt,final) /\ fn_has_code st final func /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var dst /\ sb < dimword (:256) /\ d < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready /\ 32 <= sz /\
  abi_decoder_budget first last b cap initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_scratch_effect first last lo hi st.cs_next_var limit_st d sz b cap initial ready /\
  abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] initial ready /\
  (alloca_inv initial ==> alloca_inv ready) /\ abi_encoder_extend_sim ctx func initial ready
Proof
  strip_tac >> drule_all abi_encoder_array_count_raw_transport >> strip_tac >>
  drule_all abi_encoder_array_count_registered >>
  disch_then (qspec_then `abi_decoder_ids lo hi` strip_assume_tac) >>
  drule_all abi_encoder_array_count_extend >> disch_then (qspec_then `ctx` assume_tac) >>
  asm_simp_tac bool_ss [] >> irule abi_scratch_leaf_effect >> asm_simp_tac bool_ss [] >>
  irule abi_decode_frame_widen >> qexistsl_tac [`d`,`32`] >> simp[]
QED

Theorem abi_encoder_shared_array_count_input_facts:
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) s ==>
  mload sb s = n2w (LENGTH avs) /\ sb < dimword (:256) /\ d < dimword (:256) /\
  32 <= sz /\ abi_footprint_disjoint sb source_cap [(d,32)]
Proof
  strip_tac >> drule abi_encoder_shared_array_input_facts >> strip_tac >>
  `LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) ty) avs` by
    (drule abi_encoder_structural_list_layout >> simp[]) >>
  drule abi_encoder_open_array_length >> disch_tac >>
  qpat_assum `abi_encoder_shared_input _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_input_def]) >>
  gvs[mem_word_at_eq_mload, abi_encoder_zero_aware_separation, Excl "enc_def"] >>
  simp[abi_footprint_disjoint_def] >> decide_tac
QED

Theorem abi_encoder_shared_array_count_input:
  abi_decode_array_header dst src MLOAD st = (cnt,final) /\
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready ==>
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (final,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) ready /\
  abi_encoder_array_prefix ty avs 0 d ready.vs_memory /\
  abi_decoder_operand_live final.cs_next_var cnt /\ eval_operand cnt ready = SOME (n2w (LENGTH avs))
Proof
  strip_tac >> drule abi_encoder_shared_array_count_input_facts >> strip_tac >>
  qpat_assum `abi_encoder_shared_input _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_input_def]) >>
  drule_all abi_encoder_array_count_raw_transport >> strip_tac >>
  drule abi_encoder_array_count_live >> disch_tac >>
  `abi_decode_footprint_frame [(d,32)] initial ready` by fs[abi_decode_frame_footprint] >>
  `mem_bytes_at sb source_cap initial.vs_memory = mem_bytes_at sb source_cap ready.vs_memory` by
    (drule_all abi_decode_footprint_frame_slice >> simp[]) >>
  `abi_encoder_open_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    sb source_cap ready.vs_memory` by
    (drule_all abi_encoder_open_input_mem_agree >> simp[]) >>
  `st.cs_next_var <= final.cs_next_var` by
    (drule (Q.INST [`opc` |-> `MLOAD`] abi_decode_array_header_shape) >>
     simp[abi_decode_source_opcode_def]) >>
  `eval_operand src ready = SOME (n2w sb) /\ eval_operand dst ready = SOME (n2w d)` by
    (conj_tac >> first_x_assum irule >> simp[]) >>
  `abi_decoder_operand_live final.cs_next_var src /\ abi_decoder_operand_live final.cs_next_var dst` by
    (conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  asm_simp_tac bool_ss [abi_encoder_shared_input_def, abi_encoder_array_prefix_empty] >>
  fs[abi_decoder_child_scratch_def]
QED

(* Open array-prefix algebra.  No execution and no aggregate ABI typing. *)
Theorem abi_encoder_open_array_prefix_lengths[local]:
  LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) ty) avs /\
  j <= LENGTH avs ==>
  LENGTH (FLAT (abi_tuple_heads (LENGTH avs*abi_member_head_size ty) 0
    (REPLICATE j ty) (TAKE j avs))) = j*abi_member_head_size ty /\
  LENGTH (FLAT (abi_tuple_tails (REPLICATE j ty) (TAKE j avs))) =
    SUM (MAP (abi_member_tail_size ty) (TAKE j avs))
Proof
  strip_tac >>
  `LIST_REL abi_encoder_layout_valid (REPLICATE j ty) (TAKE j avs)` by
    (gvs[LIST_REL_EL_EQN, LENGTH_TAKE, EL_REPLICATE, EL_TAKE] >> metis_tac[]) >>
  conj_tac
  >- (simp[abi_encoder_open_heads_length] >>
      mp_tac (Q.SPECL [`TAKE j avs`,`ty`] abi_encoder_uniform_sizes) >> simp[]) >>
  simp[abi_tuple_tails_length] >>
  mp_tac (Q.SPECL [`TAKE j avs`,`ty`] abi_encoder_uniform_sizes) >> simp[]
QED

Theorem abi_encoder_open_array_prefix_old_frame[local]:
  LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) ty) avs /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_decode_footprint_frame fp initial actual /\
  abi_footprint_disjoint d 32 fp /\
  abi_footprint_disjoint (d+32) (j*abi_member_head_size ty) fp /\
  abi_footprint_disjoint (d+32+LENGTH avs*abi_member_head_size ty)
    (SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) fp ==>
  abi_encoder_array_prefix ty avs j d actual.vs_memory
Proof
  strip_tac >> `j <= LENGTH avs` by fs[abi_encoder_array_prefix_def] >>
  drule_all abi_encoder_open_array_prefix_lengths >> strip_tac >>
  irule abi_encoder_array_prefix_frame >> qexistsl_tac [`fp`,`initial`] >>
  fs[AC ADD_ASSOC ADD_COMM]
QED

Theorem abi_encoder_open_array_static_step:
  LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) ty) avs /\
  j < LENGTH avs /\ ~is_dynamic ty /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_decode_footprint_frame fp initial actual /\
  abi_footprint_disjoint d 32 fp /\
  abi_footprint_disjoint (d+32) (j*abi_member_head_size ty) fp /\
  abi_footprint_disjoint (d+32+LENGTH avs*abi_member_head_size ty)
    (SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) fp /\
  mem_bytes_at (d+32+j*abi_member_head_size ty) (LENGTH (enc ty (EL j avs)))
    actual.vs_memory = enc ty (EL j avs) ==>
  abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory
Proof
  strip_tac >> `j <= LENGTH avs` by decide_tac >>
  drule_all abi_encoder_open_array_prefix_lengths >> strip_tac >>
  drule_all abi_encoder_open_array_prefix_old_frame >> disch_tac >>
  `mem_word_at d actual.vs_memory = n2w (LENGTH avs) /\
   abi_encoder_tuple_prefix (LENGTH avs*abi_member_head_size ty)
     (REPLICATE j ty) (TAKE j avs) (d+32) actual.vs_memory` by
    fs[abi_encoder_array_prefix_def] >>
  irule abi_encoder_array_prefix_advance >> simp[] >>
  irule abi_encoder_tuple_prefix_append >>
  asm_simp_tac (srw_ss()) [] >> simp[mem_bytes_at_def]
QED

Theorem abi_encoder_open_array_dynamic_step:
  LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) ty) avs /\
  j < LENGTH avs /\ is_dynamic ty /\
  off = LENGTH avs*abi_member_head_size ty+
    SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_decode_footprint_frame fp initial actual /\
  abi_footprint_disjoint d 32 fp /\
  abi_footprint_disjoint (d+32) (j*abi_member_head_size ty) fp /\
  abi_footprint_disjoint (d+32+LENGTH avs*abi_member_head_size ty)
    (SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) fp /\
  mem_word_at (d+32+j*abi_member_head_size ty) actual.vs_memory = n2w off /\
  mem_bytes_at (d+32+off) (LENGTH (enc ty (EL j avs))) actual.vs_memory =
    enc ty (EL j avs) ==>
  abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory
Proof
  strip_tac >> `j <= LENGTH avs` by decide_tac >>
  drule_all abi_encoder_open_array_prefix_lengths >> strip_tac >>
  drule_all abi_encoder_open_array_prefix_old_frame >> disch_tac >>
  `mem_word_at d actual.vs_memory = n2w (LENGTH avs) /\
   abi_encoder_tuple_prefix (LENGTH avs*abi_member_head_size ty)
     (REPLICATE j ty) (TAKE j avs) (d+32) actual.vs_memory` by
    fs[abi_encoder_array_prefix_def] >>
  irule abi_encoder_array_prefix_advance >> simp[] >>
  irule abi_encoder_tuple_prefix_append >>
  asm_simp_tac (srw_ss()) [LENGTH_enc_number, ADD_ASSOC] >>
  simp[abi_encoder_word_window, enc_number_def] >>
  qpat_x_assum `off = _` SUBST_ALL_TAC >>
  full_simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]
QED

(* Open-array prefix preservation across a restricted initializer scratch frame. *)
Theorem abi_encoder_shared_array_prefix_scratch:
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_decode_footprint_frame
    (abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial) initial actual /\
  first <= lo /\ hi <= last ==>
  abi_encoder_array_prefix ty avs j d actual.vs_memory
Proof
  strip_tac >> irule abi_encoder_open_array_prefix_output_frame >>
  conj_tac >- (drule abi_encoder_shared_array_input_facts >> strip_tac >>
    irule abi_encoder_structural_list_layout >> simp[]) >>
  qexistsl_tac [`abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial`,`initial`,`sz`] >>
  asm_simp_tac bool_ss [] >> conj_tac >- fs[abi_encoder_shared_input_def] >>
  irule abi_scratch_disjoint_subset >> qexists_tac `abi_decoder_ids first last` >>
  fs[abi_encoder_shared_input_def, SUBSET_DEF, abi_decoder_ids_def] >> decide_tac
QED

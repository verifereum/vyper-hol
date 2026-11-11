(* Counted finite encoder array loops on their physical states. *)
Theory bodyIntCallEncoderCountedArrays
Ancestors
  abiScratchArrayEntry abiEncoderArrayBodyCode abiDecodeRanges
  abiEncoderArrayExit abiEncoderArrayContext abiEncoderSequence emitHelperProps abiBuiltinPrefix exprLoweringProps instIdxIndep bodyIntCallDecoderCountedPrimitive
  abiScratchArrayLoopRun abiScratchPhaseCompose bodyIntCallDecoderCountedLoopEntry
  abiEncoderArrayParent abiEncoderComplexPrefix abiDecoderFootprint abiDecoderAllocation
  bodyIntCallEncoderCountedPrefix abiScratchOwnedPrefix abiScratchPrefix
  abiEncoderArrayDynamicLoop abiEncoderInput abiEncoderArrayFrame abiEncoderArrayTailInit abiScratchArrayTail abiScratchStatic abiScratchPrefixReach
  bodyIntCallDecoderCountedLoopFinite bodyIntCallEncoderCountedArrayPhases bodyIntCallEncoderCountedPhases
  abiDecoderArrayBackedge abiDecoderLoopRegisters abiDecoderDynamicLoopSetup abiEncoderArrayHeader abiScratchArrayLoopInvariant
  fragGasPath abiEncoderArrayLoopDynamicStep abiScratchEffect abiScratchEncoderContract abiEncoderArrayLoopCode abiScratchAddress abiScratchInput abiEncoderArrayHeaderMemory
  abiEncoderMembersDefs abiDecoderReentry abiDecoderLoop compileEnv
  venomState venomExecSemantics valueEncoding contractABI words list arithmetic

Theorem intcall_scratch_array_header:
  lookup_block hdr func.fn_blocks = SOME <|bb_label := hdr; bb_instructions :=
    abi_encode_array_header_insts id ip count_op (STRING #"%" (toString st.cs_next_var))
      (STRING #"%" (toString (st.cs_next_var+1))) (STRING #"%" (toString (st.cs_next_var+2)))
      body_lbl exit_lbl|> /\
  initial.vs_current_bb = hdr /\ initial.vs_inst_idx = 0 /\ ~initial.vs_halted /\
  abi_encoder_cursor T ip site slot first lo st j initial /\ j <= n /\ n < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var count_op /\ eval_operand count_op initial = SOME (n2w n) /\
  st.cs_next_id <= last /\ st.cs_next_var+3 <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ abi_decoder_budget first last b cap initial ==>
  ?actual. abi_decoder_address_frame st.cs_next_var initial actual /\
    fresh_vars_wrt limit_st actual /\
    (!act op cursor_site cursor_slot cursor_lo off.
      abi_encoder_cursor act op cursor_site cursor_slot first cursor_lo st off initial ==>
      abi_encoder_cursor act op cursor_site cursor_slot first cursor_lo st off actual) /\
    actual.vs_current_bb = (if j<n then body_lbl else exit_lbl) /\
    actual.vs_inst_idx = 0 /\ ~actual.vs_halted /\ gas_path ctx func initial 0 (OK actual)
Proof
  strip_tac >> drule_all abi_encoder_cursor_bounds >> strip_tac >>
  qpat_assum `abi_encoder_cursor T ip _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  `count_op <> Var (STRING #"%" (toString st.cs_next_var))` by
    (qpat_assum `abi_decoder_operand_live _ count_op`
       (mp_then Any mp_tac abi_decoder_live_excludes_output) >> simp[]) >>
  qabbrev_tac `actual = jump_to (if j<n then body_lbl else exit_lbl)
    (abi_encode_array_header_state (STRING #"%" (toString st.cs_next_var))
      (STRING #"%" (toString (st.cs_next_var+1))) (STRING #"%" (toString (st.cs_next_var+2))) j n initial)` >>
  `abi_decoder_address_frame st.cs_next_var initial actual` by
    simp[Abbr `actual`, abi_encode_array_header_address_frame] >>
  `!act op cursor_site cursor_slot cursor_lo off.
    abi_encoder_cursor act op cursor_site cursor_slot first cursor_lo st off initial ==>
    abi_encoder_cursor act op cursor_site cursor_slot first cursor_lo st off actual` by
    (rpt gen_tac >> strip_tac >>
     irule abi_encoder_cursor_address >> qexistsl_tac [`initial`, `st`] >> simp[]) >>
  `fresh_vars_wrt limit_st actual` by
    (simp_tac bool_ss [Abbr `actual`, abi_decoder_fresh_jump] >>
     irule abi_encode_array_header_registers >> simp[]) >>
  `gas_path ctx func initial 0 (OK actual)` by
    (simp_tac bool_ss [Abbr `actual`] >> irule intcall_encoder_array_header_path >>
     simp[] >> qexistsl_tac [`count_op`, `id`, `ip`, `n2w slot:bytes32`] >> simp[w2n_n2w]) >>
  qexists_tac `actual` >> simp[Abbr `actual`, jump_to_def, abi_encode_array_header_state_def, update_var_def]
QED

Theorem intcall_scratch_array_loop_header:
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
  abi_scratch_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) j origin initial ==>
  ?ready. abi_scratch_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op
      (if j < LENGTH avs then FST (SND labels) else SND (SND labels)) j origin ready /\
    gas_path ctx func initial 0 (OK ready)
Proof
  strip_tac >> drule abi_scratch_array_loop_inv_facts >> strip_tac >>
  qpat_assum `abi_scratch_array_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_array_loop_inv_def]) >>
  qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_code_def]) >>
  `owner_st.cs_next_id <= last /\ owner_st.cs_next_var+3 <= limit_st.cs_next_var` by decide_tac >>
  drule_all intcall_scratch_array_header >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_encoder_cursor T ip site slot first site owner_st j actual /\
   abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first site owner_st
     (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) actual` by
    (conj_tac >> first_x_assum irule >> simp[]) >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap initial actual` by
    (irule abi_scratch_address_effect >> simp[]) >>
  `owner_st.cs_next_var <= owner_st.cs_next_var` by simp[] >>
  drule_all abi_scratch_input_effect >> disch_tac >>
  `abi_encoder_array_prefix ty avs j d actual.vs_memory` by
    (qpat_assum `abi_decoder_address_frame _ initial actual`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >> simp[]) >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap origin actual` by
    (irule abi_scratch_effect_trans >> simp[] >> qexists_tac `initial` >> simp[]) >>
  `eval_operand count_op actual = SOME (n2w (LENGTH avs))` by
    (qpat_assum `abi_decoder_address_frame _ initial actual`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >> simp[]) >>
  qexists_tac `actual` >> simp[abi_scratch_array_loop_inv_def]
QED

Theorem intcall_scratch_array_loop_dynamic_step:
  (!value resources cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_member_core_pre value resources (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,cd,cs,cst,cen,co) r u) /\
  P ei /\ abi_scratch_encoder ei /\
  abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz body_st = (idx,body_end) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
  abi_scratch_array_loop_inv ei asz msz T ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) j origin initial /\
  j < LENGTH avs ==>
  ?actual n. abi_scratch_array_loop_inv ei asz msz T ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) (SUC j) origin actual /\
    gas_path ctx func initial n (OK actual)
Proof
  strip_tac >> drule_all intcall_scratch_array_loop_header >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_assum `j < LENGTH avs` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th, COND_CLAUSES]) >> assume_tac th) >>
  qpat_assum `abi_scratch_array_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ready`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_array_loop_inv_def]) >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ origin ready`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  drule abi_encoder_array_loop_header_phi >> disch_then (qx_choose_then `hdr_bb` strip_assume_tac) >>
  qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_code_def]) >>
  `owner_st.cs_next_var <= body_st.cs_next_var /\ owner_st.cs_next_id <= body_st.cs_next_id /\
   body_end.cs_next_id+3 <= last` by decide_tac >>
  `ready.vs_current_bb = body_st.cs_current_bb /\
   ready.vs_inst_idx = LENGTH body_st.cs_current_insts /\ site < cursor_site` by
    (fs[]) >>
  qmatch_asmsub_abbrev_tac `lookup_block body_end.cs_current_bb func.fn_blocks = SOME back_bb` >>
  `back_bb.bb_instructions = body_end.cs_current_insts ++
    abi_decode_backedge_insts body_end.cs_next_id (STRING #"%" (toString body_st.cs_next_var))
      (STRING #"%" (toString body_end.cs_next_var)) ip (FST labels)` by simp[Abbr `back_bb`] >>
  drule_all intcall_scratch_array_dynamic_round >> strip_tac >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap ready actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `body_end.cs_next_id+3`, `site`, `owner_st.cs_next_var`, `output_size`] >>
     simp[] >> decide_tac) >>
  `abi_scratch_array_loop_inv ei asz msz T ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) (SUC j) origin actual` by
    (irule abi_scratch_array_loop_inv_advance >> simp[] >>
     qexistsl_tac [`ready`, `j`, `FST (SND labels)`] >> simp[]) >>
  `?k. gas_path ctx func initial k (OK actual)` by metis_tac[gas_path_then, ADD_CLAUSES] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem intcall_scratch_array_loop_exit:
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
  abi_scratch_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) (LENGTH avs) origin initial ==>
  ?actual n. abi_scratch_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op
      (SND (SND labels)) (LENGTH avs) origin actual /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >> drule_all intcall_scratch_array_loop_header >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`ready`, `0`] >> fs[]
QED

Theorem intcall_scratch_array_dynamic_finite_loop:
  (!value resources cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_member_core_pre value resources (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,cd,cs,cst,cen,co) r u) /\
  P ei /\ abi_scratch_encoder ei /\
  abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz body_st = (idx,body_end) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
  abi_scratch_array_loop_inv ei asz msz T ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) i origin initial ==>
  ?actual n. abi_scratch_array_loop_inv ei asz msz T ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op
      (SND (SND labels)) (LENGTH avs) origin actual /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >>
  `i <= LENGTH avs` by (drule abi_scratch_array_loop_inv_facts >> simp[]) >>
  irule intcall_gas_path_finite_iteration >>
  qexistsl_tac [`i`, `\j s. abi_scratch_array_loop_inv ei asz msz T ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) j origin s`, `LENGTH avs`] >>
  asm_simp_tac bool_ss [] >> conj_tac
  >- (rpt strip_tac >> drule_all intcall_scratch_array_loop_dynamic_step >> simp[]) >>
  rpt strip_tac >> drule_all intcall_scratch_array_loop_exit >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> metis_tac[]
QED

Theorem intcall_scratch_array_loop_static_step:
  (!value resources cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_member_core_pre value resources (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,cd,cs,cst,cen,co) r u) /\
  P ei /\ abi_encoder_static_leaf ei /\
  abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
  abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) j origin initial /\
  j < LENGTH avs ==>
  ?actual n. abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) (SUC j) origin actual /\
    gas_path ctx func initial n (OK actual)
Proof
  strip_tac >> drule_all intcall_scratch_array_loop_header >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_assum `j < LENGTH avs` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th, COND_CLAUSES]) >> assume_tac th) >>
  qpat_assum `abi_scratch_array_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ready`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_array_loop_inv_def]) >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ origin ready`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  drule abi_encoder_array_loop_header_phi >> disch_then (qx_choose_then `hdr_bb` strip_assume_tac) >>
  qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_code_def]) >>
  `owner_st.cs_next_var <= body_st.cs_next_var /\ owner_st.cs_next_id <= body_st.cs_next_id /\
   body_end.cs_next_id+3 <= last` by decide_tac >>
  `ready.vs_current_bb = body_st.cs_current_bb /\
   ready.vs_inst_idx = LENGTH body_st.cs_current_insts` by simp[] >>
  qmatch_asmsub_abbrev_tac `lookup_block body_end.cs_current_bb func.fn_blocks = SOME back_bb` >>
  `back_bb.bb_instructions = body_end.cs_current_insts ++
    abi_decode_backedge_insts body_end.cs_next_id (STRING #"%" (toString body_st.cs_next_var))
      (STRING #"%" (toString body_end.cs_next_var)) ip (FST labels)` by simp[Abbr `back_bb`] >>
  drule_all intcall_scratch_array_static_round >> strip_tac >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap ready actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `body_end.cs_next_id+3`, `site`, `owner_st.cs_next_var`, `output_size`] >>
     simp[] >> decide_tac) >>
  `abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) (SUC j) origin actual` by
    (irule abi_scratch_array_loop_inv_advance >> simp[abi_encoder_cursor_def] >>
     qexistsl_tac [`ready`, `j`, `FST (SND labels)`] >> simp[]) >>
  `?k. gas_path ctx func initial k (OK actual)` by metis_tac[gas_path_then, ADD_CLAUSES] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem intcall_scratch_array_static_finite_loop:
  (!value resources cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_member_core_pre value resources (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,cd,cs,cst,cen,co) r u) /\
  P ei /\ abi_encoder_static_leaf ei /\
  abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
  abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) i origin initial ==>
  ?actual n. abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op
      (SND (SND labels)) (LENGTH avs) origin actual /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >>
  `i <= LENGTH avs` by (drule abi_scratch_array_loop_inv_facts >> simp[]) >>
  irule intcall_gas_path_finite_iteration >>
  qexistsl_tac [`i`, `\j s. abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) j origin s`, `LENGTH avs`] >>
  asm_simp_tac bool_ss [] >> conj_tac
  >- (rpt strip_tac >> drule_all intcall_scratch_array_loop_static_step >> simp[]) >>
  rpt strip_tac >> drule_all intcall_scratch_array_loop_exit >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> metis_tac[]
QED

Theorem intcall_scratch_array_loop_enter:
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    owner_st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first site owner_st 0 initial /\
  abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first site owner_st
    (LENGTH avs*abi_member_head_size ty) initial /\
  (active ==> site < cursor_site) /\ abi_decoder_operand_live owner_st.cs_next_var count_op /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  fresh_vars_wrt limit_st initial /\ abi_decoder_budget first last b cap initial /\
  initial.vs_current_bb = owner_st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH owner_st.cs_current_insts /\ ~initial.vs_halted ==>
  abi_scratch_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op
    (FST labels) 0 initial (jump_to (FST labels) initial) /\
  gas_path ctx func initial 0 (OK (jump_to (FST labels) initial))
Proof
  strip_tac >> drule_all abi_scratch_array_loop_enter >> strip_tac >> simp[] >>
  irule intcall_decoder_entry_jump_path >>
  qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_array_loop_code_def]) >>
  simp[] >> qexists_tac `owner_st.cs_next_id` >> simp[]
QED

Theorem intcall_encoder_builtin_prefix_counted:
  abi_builtin_prefix st final limit_st initial encoded /\ eval_operand out encoded = SOME w /\
  final.cs_blocks = st.cs_blocks /\ final.cs_current_bb = st.cs_current_bb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st final) /\
  fn_has_code st final func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. eval_operand out actual = SOME w /\ fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  `isPREFIX st.cs_current_insts final.cs_current_insts` by fs[inst_extends_def] >>
  drule_all intcall_same_block_seq_path >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all abi_encoder_run_sequence_reach >> strip_tac >>
  qexistsl_tac [`encoded with vs_inst_idx := LENGTH final.cs_current_insts`, `n`] >>
  gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx]
QED

Theorem intcall_encoder_array_static_exit_counted:
  abi_encode_array_static_exit src asz st = (out,final) /\ fn_has_code st final func /\
  eval_operand src initial = SOME (n2w sb) /\ mload sb initial = n2w cnt /\
  sb < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. eval_operand out actual = SOME (n2w (32+cnt*asz)) /\ fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >> drule (cj 1 abi_encode_array_exit_shape) >> strip_tac >>
  drule_all abi_encode_array_static_exit_sequence >> strip_tac >>
  drule_all intcall_encoder_builtin_prefix_counted >> simp[]
QED

Theorem intcall_encoder_array_dynamic_exit_counted:
  abi_encode_array_dynamic_exit src dyn_ptr st = (out,final) /\ fn_has_code st final func /\
  eval_operand src initial = SOME src_word /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ mload slot initial = n2w offset /\
  slot < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. eval_operand out actual = SOME (n2w (32+offset)) /\ fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >> drule (cj 2 abi_encode_array_exit_shape) >> strip_tac >>
  drule_all abi_encode_array_dynamic_exit_sequence >> strip_tac >>
  drule_all intcall_encoder_builtin_prefix_counted >> simp[]
QED


Theorem intcall_scratch_array_static_scalar_exit:
  abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op label (LENGTH avs) origin initial /\
  abi_encode_array_static_exit src asz st = (out,final) /\ fn_has_code st final func /\
  owner_st.cs_next_var <= st.cs_next_var /\ hi <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  label = st.cs_current_bb /\ st.cs_current_insts = [] ==>
  ?actual n. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap origin actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ gas_path ctx func initial n (OK actual)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_scratch_array_loop_output >> strip_tac >>
  drule abi_scratch_array_loop_inv_facts >> strip_tac >>
  qpat_assum `abi_scratch_array_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_array_loop_inv_def]) >>
  drule abi_scratch_array_input_facts >> strip_tac >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  `~is_dynamic ty` by fs[] >> drule_all abi_encoder_array_static_size >> disch_tac >>
  mp_tac (Q.INST [`cnt` |-> `LENGTH (avs:abi_value list)`] intcall_encoder_array_static_exit_counted) >>
  impl_tac >- asm_simp_tac (srw_ss()) [Excl "enc_def"] >> strip_tac >>
  `abi_scratch_effect first last site hi st.cs_next_var limit_st d output_size b cap initial actual` by
    (irule abi_scratch_address_effect >> asm_simp_tac bool_ss []) >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `hi`, `site`, `st.cs_next_var`, `output_size`] >> simp[]) >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap origin actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
     qexists_tac `initial` >> asm_simp_tac bool_ss []) >>
  qexistsl_tac [`actual`, `n`] >> fs[abi_decoder_address_frame_def, Excl "enc_def"]
QED

Theorem intcall_scratch_array_dynamic_scalar_exit:
  abi_scratch_array_loop_inv ei asz msz T ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op label (LENGTH avs) origin initial /\
  abi_encode_array_dynamic_exit src dyn_ptr st = (out,final) /\ fn_has_code st final func /\
  owner_st.cs_next_var <= st.cs_next_var /\ owner_st.cs_next_id <= last /\ hi <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ label = st.cs_current_bb /\ st.cs_current_insts = [] ==>
  ?actual n. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap origin actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ gas_path ctx func initial n (OK actual)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_scratch_array_loop_output >> strip_tac >>
  drule abi_scratch_array_loop_inv_facts >> strip_tac >>
  qpat_assum `abi_scratch_array_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_array_loop_inv_def]) >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  qpat_assum `abi_encoder_cursor T dyn_ptr cursor_site cursor_slot first site owner_st
    (LENGTH (enc (Array NONE ty) (ListV avs))-32) initial`
    (mp_then Any mp_tac abi_encoder_cursor_bounds) >>
  disch_then drule_all >> strip_tac >>
  qpat_assum `abi_encoder_cursor T dyn_ptr cursor_site cursor_slot first site owner_st
    (LENGTH (enc (Array NONE ty) (ListV avs))-32) initial`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  `abi_decoder_operand_live st.cs_next_var dyn_ptr` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `owner_st.cs_next_var` >> simp[]) >>
  `32+(LENGTH (enc (Array NONE ty) (ListV avs))-32) = LENGTH (enc (Array NONE ty) (ListV avs))` by
    (drule canonical_array_length >> strip_tac >> full_simp_tac bool_ss [] >> decide_tac) >>
  mp_tac (Q.INST [`src_word` |-> `n2w sb:bytes32`, `slot` |-> `cursor_slot:num`,
    `offset` |-> `LENGTH (enc (Array NONE ty) (ListV avs))-32`] intcall_encoder_array_dynamic_exit_counted) >>
  impl_tac >- asm_simp_tac (srw_ss()) [Excl "enc_def"] >> strip_tac >>
  `abi_scratch_effect first last site hi st.cs_next_var limit_st d output_size b cap initial actual` by
    (irule abi_scratch_address_effect >> asm_simp_tac bool_ss []) >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `hi`, `site`, `st.cs_next_var`, `output_size`] >> simp[]) >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap origin actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
     qexists_tac `initial` >> asm_simp_tac bool_ss []) >>
  qexistsl_tac [`actual`, `n`] >> fs[abi_decoder_address_frame_def, Excl "enc_def"]
QED

Theorem intcall_scratch_array_index_prepare:
  abi_decode_index_init st = (index_ptr,st') /\ fn_has_code st st' func /\
  abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ st'.cs_next_id <= last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot n. abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
      st' src dst sb source_cap d output_size first last b cap actual /\
    abi_encoder_array_prefix ty avs 0 d actual.vs_memory /\
    abi_encoder_cursor T index_ptr st.cs_next_id slot first st.cs_next_id st' 0 actual /\
    abi_scratch_effect first last st.cs_next_id st'.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >>
  `abi_encode_complex_prefix ([]:(abi_enc_info # num # num # bool) list) st = (index_ptr,st')` by
    asm_simp_tac bool_ss [GSYM abi_decode_index_init_complex_prefix] >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  `st.cs_next_id < st'.cs_next_id /\ st.cs_next_var <= st'.cs_next_var` by decide_tac >>
  `st.cs_next_id IN abi_decoder_ids first last` by (simp[abi_decoder_ids_def] >> decide_tac) >>
  `FINITE (abi_decoder_ids first last)` by simp[] >>
  drule_all (Q.INST [`ids` |-> `abi_decoder_ids first last`] intcall_scratch_encoder_prefix_counted) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all abi_scratch_owned_prefix_frame >> disch_tac >>
  drule_all abi_scratch_prefix_effect >> disch_then (qspecl_then [`output_size`, `d`] assume_tac) >>
  `st.cs_next_var <= st.cs_next_var` by simp[] >>
  drule_all abi_scratch_input_effect >> disch_tac >>
  drule_all abi_scratch_prefix_cursor >> strip_tac >>
  `abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st' src dst sb source_cap d output_size first last b cap actual` by
    (irule abi_scratch_input_mono >> qexists_tac `st` >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ initial`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  drule abi_encoder_input_typed >> disch_tac >>
  drule_all abi_encoder_array_prefix_output_frame >> disch_tac >>
  qexistsl_tac [`actual`, `slot`, `n`] >> gvs[]
QED

Theorem intcall_scratch_array_tail_init_reach:
  abi_encode_array_tail_init count_op asz st = (dyn_ptr,st') /\ fn_has_code st st' func /\
  eval_operand count_op initial = SOME (n2w cnt) /\ abi_decoder_operand_live st.cs_next_var count_op /\
  abi_decoder_budget first last b cap initial /\
  first <= st.cs_next_id /\ st'.cs_next_id <= last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. abi_encoder_complex_prefix_post [(AbiPrimWord,cnt*asz,0,F)] dyn_ptr
      st.cs_next_var st.cs_next_id limit_st first last b cap initial actual /\
    abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids st.cs_next_id st'.cs_next_id) b cap initial)
      initial actual /\
    (!op site slot lo off. abi_encoder_cursor T op site slot first lo st off initial ==>
      abi_encoder_cursor T op site slot first lo st' off actual) /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >> drule_all abi_scratch_array_tail_sequence >> strip_tac >>
  drule abi_encode_array_tail_init_shape >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') initial = OK encoded` >>
  `~encoded.vs_halted` by fs[abi_encoder_complex_prefix_post_def] >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by fs[inst_extends_def] >>
  drule_all intcall_same_block_seq_path >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all abi_encoder_run_sequence_reach >> strip_tac >>
  qabbrev_tac `actual = encoded with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  `abi_encoder_complex_prefix_post [(AbiPrimWord,cnt*asz,0,F)] dyn_ptr
    st.cs_next_var st.cs_next_id limit_st first last b cap initial actual /\
   abi_decode_footprint_frame
    (abi_decoder_child_scratch (abi_decoder_ids st.cs_next_id st'.cs_next_id) b cap initial)
    initial actual` by simp[Abbr `actual`, abi_scratch_inst_idx] >>
  `st.cs_next_var <= st'.cs_next_var /\ st.cs_next_id <= st'.cs_next_id` by decide_tac >>
  `!op site slot lo off. abi_encoder_cursor T op site slot first lo st off initial ==>
    abi_encoder_cursor T op site slot first lo st' off actual` by
    (rpt gen_tac >> strip_tac >> drule_all abi_scratch_owned_prefix_parent >> simp[]) >>
  qexistsl_tac [`actual`, `n`] >> gvs[Abbr `actual`, abi_scratch_inst_idx]
QED

Theorem intcall_scratch_array_tail_init_prepare:
  abi_encode_array_tail_init count_op asz st = (dyn_ptr,st') /\ fn_has_code st st' func /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  abi_decoder_operand_live st.cs_next_var count_op /\
  abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ st'.cs_next_id <= last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot n. abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
      st' src dst sb source_cap d output_size first last b cap actual /\
    abi_encoder_array_prefix ty avs 0 d actual.vs_memory /\
    abi_encoder_cursor T dyn_ptr st.cs_next_id slot first st.cs_next_id st' (LENGTH avs*asz) actual /\
    (!op cursor_site cursor_slot cursor_lo off.
      abi_encoder_cursor T op cursor_site cursor_slot first cursor_lo st off initial ==>
      abi_encoder_cursor T op cursor_site cursor_slot first cursor_lo st' off actual) /\
    abi_scratch_effect first last st.cs_next_id st'.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >> drule_all intcall_scratch_array_tail_init_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule abi_encode_array_tail_init_shape >> strip_tac >>
  `st.cs_next_id < st'.cs_next_id /\ st.cs_next_var <= st'.cs_next_var` by decide_tac >>
  drule_all abi_scratch_prefix_effect >> disch_then (qspecl_then [`output_size`, `d`] assume_tac) >>
  `st.cs_next_var <= st.cs_next_var` by simp[] >>
  drule_all abi_scratch_input_effect >> disch_tac >>
  `abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st' src dst sb source_cap d output_size first last b cap actual` by
    (irule abi_scratch_input_mono >> qexists_tac `st` >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ initial`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  drule abi_encoder_input_typed >> disch_tac >>
  drule_all abi_encoder_array_prefix_output_frame >> disch_tac >>
  `abi_decoder_operand_live st'.cs_next_var dyn_ptr` by
    (asm_simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     rpt strip_tac >> decide_tac) >>
  qpat_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
  `abi_encoder_cursor T dyn_ptr st.cs_next_id slot first st.cs_next_id st' (LENGTH avs*asz) actual` by
    simp[abi_encoder_cursor_def] >>
  qexistsl_tac [`actual`, `slot`, `n`] >> asm_simp_tac bool_ss []
QED

Theorem intcall_scratch_array_dynamic_init_prepare:
  abi_encode_array_dynamic_init count_op asz start = (ptrs,owner_st) /\ fn_has_code start owner_st func /\
  abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
    start src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\ abi_decoder_operand_live start.cs_next_var count_op /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  owner_st.cs_next_id <= hi /\ hi <= last /\ owner_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?ready index_slot tail_slot n.
    abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
      owner_st src dst sb source_cap d output_size first last b cap ready /\
    abi_encoder_array_prefix ty avs 0 d ready.vs_memory /\
    abi_encoder_cursor T (FST ptrs) start.cs_next_id index_slot first start.cs_next_id owner_st 0 ready /\
    abi_encoder_cursor T (SND ptrs) (start.cs_next_id+2) tail_slot first start.cs_next_id owner_st
      (LENGTH avs*abi_member_head_size ty) ready /\
    abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial ready /\
    ready.vs_current_bb = owner_st.cs_current_bb /\ ready.vs_inst_idx = LENGTH owner_st.cs_current_insts /\
    ~ready.vs_halted /\ gas_path ctx func initial n (OK ready)
Proof
  strip_tac >> drule_all abi_encode_array_dynamic_init_context >> strip_tac >>
  `after_index.cs_next_var <= limit_st.cs_next_var /\ after_index.cs_next_id <= last /\
   first <= after_index.cs_next_id /\ owner_st.cs_next_id <= last /\
   start.cs_next_var <= after_index.cs_next_var` by decide_tac >>
  drule_all intcall_scratch_array_index_prepare >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path ctx func initial n1 (OK indexed)` >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ initial indexed`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `eval_operand count_op indexed = SOME (n2w (LENGTH avs))` by
    (qpat_assum `!op w. _` irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live after_index.cs_next_var count_op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `start.cs_next_var` >> simp[]) >>
  drule_all intcall_scratch_array_tail_init_prepare >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path ctx func indexed n2 (OK ready)` >>
  `abi_encoder_cursor T ip start.cs_next_id slot first start.cs_next_id owner_st 0 ready` by
    (qpat_assum `!op cursor_site cursor_slot cursor_lo off. _` irule >> asm_simp_tac bool_ss []) >>
  `asz = abi_member_head_size ty` by fs[abi_scratch_input_def, abi_encoder_array_input_iff] >>
  `abi_encoder_cursor T dyn_ptr (start.cs_next_id+2) slot' first start.cs_next_id owner_st
    (LENGTH avs*abi_member_head_size ty) ready` by
    (gvs[abi_encoder_cursor_def] >> decide_tac) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial indexed` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `after_index.cs_next_id`, `start.cs_next_id`, `start.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap indexed ready` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `owner_st.cs_next_id`, `after_index.cs_next_id`, `after_index.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial ready` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >> qexists_tac `indexed` >> asm_simp_tac bool_ss []) >>
  `gas_path ctx func initial (n1+n2) (OK ready)` by
    (irule gas_path_then >> qexists_tac `indexed` >> simp[]) >>
  qexistsl_tac [`ready`, `slot`, `slot'`, `n1+n2`] >> asm_simp_tac (srw_ss()) []
QED

Theorem intcall_scratch_array_dynamic_loop_result:
  (!value resources cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_member_core_pre value resources (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,cd,cs,cst,cen,co) r u) /\
  P ei /\ abi_scratch_encoder ei /\
  abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz body_st = (idx,body_end) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  abi_encode_array_dynamic_exit src dyn_ptr exit_st = (out,final) /\ fn_has_code exit_st final func /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\
  body_end.cs_next_var+1 <= limit_st.cs_next_var /\ final.cs_next_var <= limit_st.cs_next_var /\
  abi_scratch_array_loop_inv ei asz msz T ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) i origin initial ==>
  ?actual n. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap origin actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >> drule_all intcall_scratch_array_dynamic_finite_loop >> strip_tac >>
  rename1 `gas_path ctx func initial n1 (OK prepared)` >>
  qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_code_def]) >>
  `owner_st.cs_next_var <= exit_st.cs_next_var /\ owner_st.cs_next_id <= last` by decide_tac >>
  `SND (SND labels) = exit_st.cs_current_bb` by simp[] >>
  drule_all intcall_scratch_array_dynamic_scalar_exit >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path ctx func prepared n2 (OK actual)` >>
  `gas_path ctx func initial (n1+n2) (OK actual)` by
    (irule gas_path_then >> qexists_tac `prepared` >> simp[]) >>
  qexistsl_tac [`actual`, `n1+n2`] >> asm_simp_tac bool_ss []
QED

Theorem intcall_scratch_array_static_loop_result:
  (!value resources cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_member_core_pre value resources (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,cd,cs,cst,cen,co) r u) /\
  P ei /\ abi_encoder_static_leaf ei /\
  abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  abi_encode_array_static_exit src asz exit_st = (out,final) /\ fn_has_code exit_st final func /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\
  body_end.cs_next_var+1 <= limit_st.cs_next_var /\ final.cs_next_var <= limit_st.cs_next_var /\
  abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) i origin initial ==>
  ?actual n. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap origin actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >> drule_all intcall_scratch_array_static_finite_loop >> strip_tac >>
  rename1 `gas_path ctx func initial n1 (OK prepared)` >>
  qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_code_def]) >>
  `owner_st.cs_next_var <= exit_st.cs_next_var` by decide_tac >>
  `SND (SND labels) = exit_st.cs_current_bb` by simp[] >>
  drule_all intcall_scratch_array_static_scalar_exit >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path ctx func prepared n2 (OK actual)` >>
  `gas_path ctx func initial (n1+n2) (OK actual)` by
    (irule gas_path_then >> qexists_tac `prepared` >> simp[]) >>
  qexistsl_tac [`actual`, `n1+n2`] >> asm_simp_tac bool_ss []
QED

Theorem intcall_scratch_array_dynamic_loop_run:
  (!value resources cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_member_core_pre value resources (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,cd,cs,cst,cen,co) r u) /\
  P ei /\ abi_scratch_encoder ei /\
  abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz body_st = (idx,body_end) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  abi_encode_array_dynamic_exit src dyn_ptr exit_st = (out,final) /\ fn_has_code exit_st final func /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\
  body_end.cs_next_var+1 <= limit_st.cs_next_var /\ final.cs_next_var <= limit_st.cs_next_var /\
  abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
    owner_st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first site owner_st 0 initial /\
  abi_encoder_cursor T dyn_ptr cursor_site cursor_slot first site owner_st
    (LENGTH avs*abi_member_head_size ty) initial /\
  site < cursor_site /\ abi_decoder_operand_live owner_st.cs_next_var count_op /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  fresh_vars_wrt limit_st initial /\ abi_decoder_budget first last b cap initial /\
  initial.vs_current_bb = owner_st.cs_current_bb /\ initial.vs_inst_idx = LENGTH owner_st.cs_current_insts /\
  ~initial.vs_halted ==>
  ?actual n. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >>
  `T ==> site < cursor_site` by simp[] >>
  drule_all (Q.INST [`active` |-> `T`, `hi` |-> `hi:num`] intcall_scratch_array_loop_enter) >>
  disch_then (qspecl_then [`hi`, `ctx`] strip_assume_tac) >>
  drule_all intcall_scratch_array_dynamic_loop_result >> strip_tac >>
  `?k. gas_path ctx func initial k (OK actual)` by metis_tac[gas_path_then, ADD_CLAUSES] >>
  qexistsl_tac [`actual`, `k`] >> asm_simp_tac bool_ss []
QED

Theorem intcall_scratch_array_static_loop_run:
  (!value resources cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_member_core_pre value resources (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,cd,cs,cst,cen,co) r u) /\
  P ei /\ abi_encoder_static_leaf ei /\
  abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  abi_encode_array_static_exit src asz exit_st = (out,final) /\ fn_has_code exit_st final func /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\
  body_end.cs_next_var+1 <= limit_st.cs_next_var /\ final.cs_next_var <= limit_st.cs_next_var /\
  abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
    owner_st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first site owner_st 0 initial /\
  abi_decoder_operand_live owner_st.cs_next_var count_op /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  fresh_vars_wrt limit_st initial /\ abi_decoder_budget first last b cap initial /\
  initial.vs_current_bb = owner_st.cs_current_bb /\ initial.vs_inst_idx = LENGTH owner_st.cs_current_insts /\
  ~initial.vs_halted ==>
  ?actual n. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >>
  `abi_encoder_cursor F ip site slot first site owner_st (LENGTH avs*abi_member_head_size ty) initial /\
   (F ==> site < site)` by simp[abi_encoder_cursor_def] >>
  drule_all (Q.INST [`active` |-> `F`, `hi` |-> `hi:num`] intcall_scratch_array_loop_enter) >>
  disch_then (qspecl_then [`hi`, `ctx`] strip_assume_tac) >>
  drule_all intcall_scratch_array_static_loop_result >> strip_tac >>
  `?k. gas_path ctx func initial k (OK actual)` by metis_tac[gas_path_then, ADD_CLAUSES] >>
  qexistsl_tac [`actual`, `k`] >> asm_simp_tac bool_ss []
QED

Theorem intcall_scratch_array_static_loop:
  (!value resources cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_member_core_pre value resources (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,cd,cs,cst,cen,co) r u) /\
  P ei /\ abi_encoder_static_leaf ei /\
  compile_abi_encode_dyn_static_loop dst src ei asz msz count_op start = (out,final) /\
  fn_has_code start final func /\
  abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
    start src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_decoder_operand_live start.cs_next_var count_op /\ eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  final.cs_next_id <= hi /\ hi <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual n. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >> drule_all abi_encode_array_static_loop_code >> strip_tac >>
  `owner_st.cs_next_id <= last /\ owner_st.cs_next_id <= hi /\ owner_st.cs_next_var <= limit_st.cs_next_var /\
   body_end.cs_next_id+3 <= hi /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
   start.cs_next_var <= owner_st.cs_next_var` by
    (qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _`
       (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_code_def]) >> decide_tac) >>
  drule_all intcall_scratch_array_index_prepare >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path ctx func initial n1 (OK ready)` >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ initial ready`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `eval_operand count_op ready = SOME (n2w (LENGTH avs))` by
    (qpat_assum `!op w. _` irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live owner_st.cs_next_var count_op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `start.cs_next_var` >> simp[]) >>
  drule_all intcall_scratch_array_static_loop_run >> strip_tac >>
  rename1 `gas_path ctx func ready n2 (OK actual)` >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial ready` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `owner_st.cs_next_id`, `start.cs_next_id`, `start.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap ready actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `hi`, `start.cs_next_id`, `owner_st.cs_next_var`, `output_size`] >> simp[]) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >> qexists_tac `ready` >> asm_simp_tac bool_ss []) >>
  `gas_path ctx func initial (n1+n2) (OK actual)` by
    (irule gas_path_then >> qexists_tac `ready` >> simp[]) >>
  qexistsl_tac [`actual`, `n1+n2`] >> asm_simp_tac bool_ss []
QED

Theorem intcall_scratch_array_dynamic_loop:
  (!value resources cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_member_core_pre value resources (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,cd,cs,cst,cen,co) r u) /\
  P ei /\ abi_scratch_encoder ei /\ compile_abi_encode_dyn_loop dst src ei asz msz count_op start = (out,final) /\
  fn_has_code start final func /\
  abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
    start src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_decoder_operand_live start.cs_next_var count_op /\ eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  final.cs_next_id <= hi /\ hi <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual n. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >> drule_all abi_encode_array_dynamic_loop_code >> strip_tac >>
  `owner_st.cs_next_id <= hi /\ owner_st.cs_next_var <= limit_st.cs_next_var /\
   body_end.cs_next_id+3 <= hi /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
   start.cs_next_var <= owner_st.cs_next_var /\ start.cs_next_id < start.cs_next_id+2` by
    (qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _`
       (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_code_def]) >> decide_tac) >>
  drule_all intcall_scratch_array_dynamic_init_prepare >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path ctx func initial n1 (OK ready)` >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ initial ready`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `eval_operand count_op ready = SOME (n2w (LENGTH avs))` by
    (qpat_assum `!op w. _` irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live owner_st.cs_next_var count_op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `start.cs_next_var` >> simp[]) >>
  drule_all intcall_scratch_array_dynamic_loop_run >> strip_tac >>
  rename1 `gas_path ctx func ready n2 (OK actual)` >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap ready actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `hi`, `start.cs_next_id`, `owner_st.cs_next_var`, `output_size`] >> simp[]) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >> qexists_tac `ready` >> asm_simp_tac bool_ss []) >>
  `gas_path ctx func initial (n1+n2) (OK actual)` by
    (irule gas_path_then >> qexists_tac `ready` >> simp[]) >>
  qexistsl_tac [`actual`, `n1+n2`] >> asm_simp_tac bool_ss []
QED

(* The selected loop retains the counted path on its physical endpoint. *)
Theorem intcall_scratch_array_selected_loop:
  (!value resources cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_member_core_pre value resources (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,cd,cs,cst,cen,co) r u) /\
  P ei /\ (if active then abi_scratch_encoder ei else abi_encoder_static_leaf ei) /\
  (if active then compile_abi_encode_dyn_loop dst src ei asz msz count_op start = (out,final)
    else compile_abi_encode_dyn_static_loop dst src ei asz msz count_op start = (out,final)) /\
  fn_has_code start final func /\
  abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    start src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_decoder_operand_live start.cs_next_var count_op /\ eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  final.cs_next_id <= hi /\ hi <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual n. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ gas_path ctx func initial n (OK actual)
Proof
  Cases_on `active` >> simp_tac bool_ss [COND_CLAUSES]
  >- (strip_tac >> drule_all intcall_scratch_array_dynamic_loop >> simp_tac bool_ss [])
  >> strip_tac >> drule_all intcall_scratch_array_static_loop >> simp_tac bool_ss []
QED

(* Parent preparation, selected loop and protected finish share counted states. *)
Theorem intcall_scratch_array_run:
  (!value resources cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_member_core_pre value resources (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,cd,cs,cst,cen,co) r u) /\
  P ei /\ (if active then abi_scratch_encoder ei else abi_encoder_static_leaf ei) /\
  compile_abi_encode_to_buf dst src (AbiDynArray ei asz msz active) start = (out,final) /\
  fn_has_code start final func /\
  abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    start src dst sb source_cap d output_size first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual n. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last start.cs_next_id final.cs_next_id start.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >> drule_all abi_encode_array_context >> strip_tac >>
  `loop_st.cs_next_id <= last /\ loop_end.cs_next_id <= last /\
   loop_st.cs_next_var <= limit_st.cs_next_var /\ loop_end.cs_next_var <= limit_st.cs_next_var /\
   start.cs_next_id < loop_st.cs_next_id /\ start.cs_next_id < final.cs_next_id /\
   first <= loop_st.cs_next_id /\ start.cs_next_var <= loop_st.cs_next_var /\
   loop_end.cs_next_id <= final.cs_next_id` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `start`, `hi` |-> `loop_st.cs_next_id`] intcall_scratch_array_parent_prepare) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> strip_tac >>
  rename1 `gas_path ctx func initial n1 (OK ready)` >>
  `fresh_vars_wrt limit_st ready /\ abi_decoder_budget first last b cap ready` by fs[abi_scratch_effect_def] >>
  mp_tac (Q.INST [`count_op` |-> `SND (ops:operand # operand)`, `start` |-> `loop_st`,
    `out` |-> `size_op`, `final` |-> `loop_end`, `initial` |-> `ready:venom_state`,
    `hi` |-> `loop_end.cs_next_id`] intcall_scratch_array_selected_loop) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  rename1 `gas_path ctx func ready n2 (OK encoded)` >>
  qpat_assum `abi_scratch_input _ _ _ loop_st _ _ _ _ _ _ _ _ _ _ ready`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  drule_all intcall_scratch_array_finish_protected >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path ctx func encoded n3 (OK actual)` >>
  mp_tac (Q.INST [`st` |-> `start`, `prepared` |-> `loop_st`, `middle` |-> `loop_end`,
    `end_st` |-> `final`, `sz` |-> `output_size:num`] abi_scratch_phase_compose) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> disch_tac >>
  `gas_path ctx func ready (n2+n3) (OK actual)` by
    (irule gas_path_then >> qexists_tac `encoded` >> simp[]) >>
  `gas_path ctx func initial (n1+(n2+n3)) (OK actual)` by
    (irule gas_path_then >> qexists_tac `ready` >> simp[]) >>
  qexistsl_tac [`actual`, `n1+(n2+n3)`] >> asm_simp_tac bool_ss []
QED

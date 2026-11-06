(* Reentry-safe guard and owned heterogeneous constructor integration. *)
Theory exprSimAbiDecodeComplexOutcome
Ancestors
  exprSimAbiDecodeAbortReentry exprSimAbiDecodeCompositePrefix
  exprSimAbiDecodeTupleTraversal exprSimAbiDecodeOwnedMember
  abiDecoderComplexGuard abiDecoderComplexHead abiDecoderReentry abiDecoderVarExtend
  abiDecoderSequenceReach abiDecoderFiniteControl
  exprSimAbiDecodeMemberExecute abiDecoderDynamicLoopSetup instIdxIndep
  abiDecoderBytestringOutcome abiDecoderSiteEffect exprSimAbiDecodeSiteProvenance
  abiEncoder compileEnv emitHelper emitHelperProps exprLoweringProps
  venomState venomInst words list rich_list arithmetic
  abiDecoderCoherence abiDecodeRanges valueEncodingProps vyperTypeSystem vyperValue

Theorem abi_decode_complex_guard_abort_opcodes[local]:
  abi_decode_complex_head_guard src hi k st = ((),st') ==>
  EVERY (\i. MEM i.inst_opcode [ADD; LT; GT; AND; ISZERO; MLOAD; ASSERT])
    (emitted_insts st st')
Proof
  Cases_on `hi = Lit 0w` >>
  simp[abi_decode_complex_head_guard_def, compile_abi_decode_range_check_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_decode_complex_head_guard_revert_reentry:
  abi_decode_complex_head_guard src hi k st = ((),st') /\
  hi <> Lit 0w /\ eval_operand src s = SOME(n2w p) /\
  eval_operand hi s = SOME(n2w H) /\
  p < dimword(:256) /\ k < dimword(:256) /\ H < dimword(:256) /\
  H < p+k /\ abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  strip_tac >>
  `fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var s)` by
    irule abi_decoder_prune_fresh >>
  `eval_operand src (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w p) /\
   eval_operand hi (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w H)` by
    asm_simp_tac bool_ss [abi_decoder_prune_eval] >>
  drule_all abi_decode_complex_head_guard_revert >> strip_tac >>
  `abi_decoder_vars_extend s.vs_vars (abi_decoder_prune_vars st.cs_next_var s) s` by
    irule abi_decoder_prune_extension >>
  drule abi_decode_complex_guard_abort_opcodes >> strip_tac >>
  drule_all abi_decode_guard_sequence_vars_extend_abort >> simp[]
QED

Theorem abi_decode_complex_head_guard_abort_reentry:
  abi_decode_complex_head_guard src hi k st = ((),st') /\
  hi <> Lit 0w /\ eval_operand src s = SOME(n2w p) /\
  eval_operand hi s = SOME(n2w H) /\
  p < dimword(:256) /\ k < dimword(:256) /\ H < dimword(:256) /\
  H < p+k /\ abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st st' fn /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u. Dabort ctx fn s Revert_abort u
Proof
  strip_tac >> drule_all abi_decode_complex_head_guard_revert_reentry >> strip_tac >>
  drule abi_decode_complex_head_guard_prefix_shape >> strip_tac >>
  drule_all abi_decoder_run_sequence_abort >> strip_tac >>
  qpat_x_assum `!ctx. _` (qspec_then `ctx` strip_assume_tac) >>
  simp[Dabort_def] >> qexistsl_tac [`t with vs_inst_idx := n`, `0`] >> simp[]
QED

Theorem abi_decode_complex_head_guard_reach_reentry:
  abi_decode_complex_head_guard src hi k st = ((),st') /\
  hi <> Lit 0w /\ eval_operand src s = SOME(n2w p) /\
  eval_operand hi s = SOME(n2w H) /\ p+k <= H /\ H < dimword(:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st st' fn /\ abi_decode_entry st s /\
  decode_site_resources ctx func s ==>
  ?t. Dreach ctx fn s t /\ fresh_vars_wrt limit_st t /\
    abi_decoder_address_frame st.cs_next_var s t /\ abi_decode_entry st' t /\
    decode_site_effect ctx func st.cs_next_var writes s t /\
    abi_decode_alloc_progress sites s t
Proof
  strip_tac >>
  drule abi_decoder_complex_guard_reentry >>
  disch_then (qspecl_then [`p`, `limit_st`, `s`] mp_tac) >>
  (impl_tac >- (simp[] >> qexists_tac `H` >> simp[])) >> strip_tac >>
  drule abi_decode_complex_head_guard_prefix_shape >> strip_tac >>
  `EVERY (\i. abi_bytes_opcode i.inst_opcode) (emitted_insts st st')` by
    (drule abi_decode_complex_guard_abort_opcodes >>
     simp[EVERY_MEM, abi_bytes_opcode_def, abiDecoderWordOutcomeTheory.abi_word_opcode_def] >>
     strip_tac >> gen_tac >> disch_tac >> first_x_assum drule >>
     rpt strip_tac >> simp[]) >>
  drule_all abi_bytes_sequence_static >> strip_tac >>
  `decode_site_resources ctx func actual` by
    (irule decode_site_resources_fields >> qexists_tac `s` >>
     fs[abi_decoder_address_frame_def, venom_state_component_equality]) >>
  `decode_site_effect ctx func st.cs_next_var writes s actual` by
    (simp[decode_site_effect_def, decode_memory_frame_def] >>
     fs[abi_decoder_address_frame_def, decode_static_frame_def,
       venom_state_component_equality]) >>
  qpat_x_assum `actual = s with <|vs_vars := _; vs_memory := _|>` kall_tac >>
  `~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts` by fs[abi_decode_entry_def] >>
  drule_all abi_decoder_run_sequence_prefix >> strip_tac >>
  qexists_tac `t` >> conj_tac >- metis_tac[Dreach_straight_prefix] >>
  gvs[abi_decode_entry_def, abi_decoder_address_frame_def, fresh_vars_wrt_def,
    eval_op_inst_idx, abi_decode_alloc_progress_def] >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem abi_decode_owned_rows_address_frame:
  abi_decode_owned_rows_pre ctx func ce env limit_st next scratch sites
    st dst src base_op hi B bs p d ao vo rows s /\
  st.cs_next_var <= ready.cs_next_var /\
  ready.cs_next_var <= limit_st.cs_next_var /\
  abi_decoder_address_frame st.cs_next_var s t /\
  fresh_vars_wrt limit_st t /\ abi_decode_entry ready t /\
  decode_site_resources ctx func t ==>
  abi_decode_owned_rows_pre ctx func ce env limit_st next scratch sites
    ready dst src base_op hi B bs p d ao vo rows t
Proof
  strip_tac >>
  `abi_decode_owned sites scratch (d+vo)
     (SUM(MAP abi_tuple_row_mem_width rows)) t` by
    metis_tac[abi_decode_owned_address_frame,
      exprSimAbiDecodeOwnedRowsTheory.abi_decode_owned_rows_pre_def] >>
  qhdtm_x_assum `abi_decode_owned_rows_pre`
    (strip_assume_tac o PURE_REWRITE_RULE
      [exprSimAbiDecodeOwnedRowsTheory.abi_decode_owned_rows_pre_def]) >>
  `EVERY (abi_decoder_operand_live ready.cs_next_var) [dst;src;base_op;hi]` by
    (fs[EVERY_DEF] >> metis_tac[abi_decoder_operand_live_mono]) >>
  `eval_operand src t = SOME(n2w p) /\ eval_operand dst t = SOME(n2w d) /\
   eval_operand base_op t = SOME(n2w B) /\
   eval_operand hi t = SOME(n2w(LENGTH bs))` by
    (fs[EVERY_DEF, abi_decoder_address_frame_def] >> metis_tac[]) >>
  simp_tac bool_ss [exprSimAbiDecodeOwnedRowsTheory.abi_decode_owned_rows_pre_def] >>
  fs[abi_decoder_address_frame_def] >> metis_tac[LESS_EQ_TRANS]
QED

(* A source-view boundary must account for zero-width types past the end. *)
Theorem abi_decode_empty_tuple_past_end_source_probe:
  LENGTH ([]:word8 list) < 1 + 0 /\
  abi_decode_source_accepts FEMPTY (TupleT [])
    (abi_decode_source_view (vyper_to_abi_type FEMPTY (TupleT [])) [] 1)
    (ArrayV (TupleV []))
Proof
  EVAL_TAC >> simp[dimword_def]
QED

Theorem abi_decode_assignable_embedded_head_positive:
  abi_decoder_coherent ce env sf ty tv /\ assignable_type env ty ==>
  0 < abi_embedded_static_size ce.ce_struct_fields ty
Proof
  strip_tac >> drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  `0 < type_slot_size tv` by metis_tac[assignable_type_slot_size_pos] >>
  `0 < type_memory_size tv` by metis_tac[type_memory_size_pos] >>
  Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
  gvs[abi_member_head_size_def]
QED

Theorem abi_decode_assignable_empty_tuple_excluded:
  ~assignable_type env (TupleT [])
Proof
  simp[assignable_type_def]
QED

Theorem abi_decode_evaluated_zero_fixed_array_excluded:
  evaluate_type env (ArrayT ty (Fixed 0)) <> SOME tv
Proof
  simp[Once evaluate_type_def] >> Cases_on `evaluate_type env ty` >> simp[]
QED

Theorem abi_decode_positive_head_short_drop:
  0 < k /\ LENGTH bs < p+k ==> LENGTH (DROP p bs) < k
Proof
  simp[LENGTH_DROP] >> decide_tac
QED

Theorem abi_decode_nonempty_positive_head_sum:
  !xs. xs <> [] /\ EVERY (\x. 0 < f x) xs ==> 0 < SUM (MAP f xs)
Proof
  Cases >> simp[] >> rpt strip_tac >> decide_tac
QED

(* Position audit: entry is zero. Static children lie inside the checked
   parent head; dynamic offsets have only a wrap check before child entry,
   so malformed offsets need not be within the source. For accepted dynamic
   children, abi_valid_dynamic_member_window supplies offset+32<=length.
   Fixed-array heads and runtime-array heads bound count*element-head;
   dynamic element offsets have the same conditional classification.
   Zero-width counterexamples do not satisfy the contextual type premises:
   assignable_type_slot_size_pos and coherence give positive member heads.
   Thus short-head rejection should use a positive constructor head, rather
   than impose an unconditional child-position invariant. *)

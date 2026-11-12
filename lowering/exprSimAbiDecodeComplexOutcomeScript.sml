(* Reentry-safe guard and owned heterogeneous constructor integration. *)
Theory exprSimAbiDecodeComplexOutcome
Ancestors
  loweringStateRelDefs
  exprSimAbiDecodeAbortReentry exprSimAbiDecodeCompositePrefix
  exprSimAbiDecodeTupleTraversal exprSimAbiDecodeOwnedMember
  exprSimAbiDecodeTupleAssembly exprSimAbiDecodeTupleOutcome abiValidMembers
  abiDecoderComplexGuard abiDecoderComplexHead abiDecoderReentry abiDecoderVarExtend
  abiDecoderSequenceReach abiDecoderFiniteControl
  exprSimAbiDecodeMemberExecute abiDecoderDynamicLoopSetup instIdxIndep
  abiDecoderBytestringOutcome abiDecoderSiteEffect exprSimAbiDecodeSiteProvenance
  abiEncoder compileEnv emitHelper emitHelperProps exprLoweringProps
  venomState venomInst words list rich_list arithmetic
  abiDecoderCoherence abiDecodeRanges valueEncodingProps vyperTypeSystem vyperValue
  vyperABI vyperTypeABI abiDecoderMembers contractABI
  abiDecoderMemberInfos abiDecoderHeadAdequacy valueEncoding valueEncodingTyping

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
  `EVERY (\i. MEM i.inst_opcode [ADD; MUL; LT; GT; AND; ISZERO; MLOAD; ASSERT])
    (emitted_insts st st')` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
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
    (simp[decode_site_effect_def, decode_memory_frame_def, decode_upper_frame_def] >>
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

Theorem abi_decode_schema_heads_positive:
  abi_tuple_rows_schema ce env rows /\ rows <> [] ==>
  0 < SUM (MAP abi_tuple_row_abi_width rows)
Proof
  strip_tac >> irule abi_decode_nonempty_positive_head_sum >> simp[] >>
  qpat_x_assum `abi_tuple_rows_schema _ _ _` mp_tac >>
  simp[abi_tuple_rows_schema_def, EVERY_MEM, pairTheory.FORALL_PROD,
    abi_tuple_row_abi_width_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all abi_decode_assignable_embedded_head_positive >>
  drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def]
QED

Theorem abi_decode_schema_head_widths:
  !rows. abi_tuple_rows_schema ce env rows ==>
  MAP abi_tuple_row_abi_width rows =
  MAP (abi_member_head_size o vyper_to_abi_type env)
    (MAP (\(ei,ty,tv,asz,msz). ty) rows)
Proof
  Induct >- simp[] >> gen_tac >> PairCases_on `h` >>
  simp[abi_tuple_rows_schema_def, abi_tuple_row_abi_width_def] >>
  metis_tac[abi_tuple_rows_schema_def]
QED

Theorem abi_decode_tuple_source_head_bound:
  abi_tuple_rows_schema ce env rows /\
  tys = MAP (\(ei,ty,tv,asz,msz). ty) rows /\
  abi_decode_source_accepts env (TupleT tys) view v ==>
  SUM (MAP abi_tuple_row_abi_width rows) <= LENGTH view
Proof
  strip_tac >> drule abi_decode_schema_head_widths >> strip_tac >>
  qpat_x_assum `abi_decode_source_accepts _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_decode_source_accepts_def, vyper_to_abi_type_def,
    Once vyper_decode_valid_enc_def] >> strip_tac >>
  drule abi_valid_members_view >>
  gvs[vyper_to_abi_types_MAP, MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem abi_decode_struct_source_head_bound:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  abi_tuple_rows_schema ce (env \\ nsid) rows /\
  MAP SND args = MAP (\(ei,ty,tv,asz,msz). ty) rows /\
  abi_decode_source_accepts env (StructT nsid) view v ==>
  SUM (MAP abi_tuple_row_abi_width rows) <= LENGTH view
Proof
  strip_tac >> drule abi_decode_schema_head_widths >> strip_tac >>
  qpat_x_assum `abi_decode_source_accepts _ _ _ _` mp_tac >>
  asm_simp_tac (srw_ss()) [abi_decode_source_accepts_def, vyper_to_abi_type_def,
    Once vyper_decode_valid_enc_def] >> strip_tac >>
  drule abi_valid_members_view >>
  gvs[vyper_to_abi_types_MAP, MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem abi_decode_source_view_length_le:
  LENGTH (abi_decode_source_view at bs p) <= LENGTH (DROP p bs)
Proof
  Cases_on `is_dynamic at` >> simp[abi_decode_source_view_def, LENGTH_TAKE_EQ]
QED

Theorem abi_decode_tuple_short_head_reject:
  abi_tuple_rows_schema ce env rows /\ rows <> [] /\
  tys = MAP (\(ei,ty,tv,asz,msz). ty) rows /\
  LENGTH bs < p + SUM (MAP abi_tuple_row_abi_width rows) ==>
  ~(?v. abi_decode_source_accepts env (TupleT tys)
    (abi_decode_source_view (vyper_to_abi_type env (TupleT tys)) bs p) v)
Proof
  strip_tac >> drule_all abi_decode_schema_heads_positive >> strip_tac >>
  drule_all abi_decode_positive_head_short_drop >> strip_tac >>
  strip_tac >> drule_all abi_decode_tuple_source_head_bound >>
  strip_tac >>
  `LENGTH (abi_decode_source_view (vyper_to_abi_type env (TupleT tys)) bs p)
    <= LENGTH (DROP p bs)` by irule abi_decode_source_view_length_le >> decide_tac
QED

Theorem abi_decode_struct_short_head_reject:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  abi_tuple_rows_schema ce (env \\ nsid) rows /\ rows <> [] /\
  MAP SND args = MAP (\(ei,ty,tv,asz,msz). ty) rows /\
  LENGTH bs < p + SUM (MAP abi_tuple_row_abi_width rows) ==>
  ~(?v. abi_decode_source_accepts env (StructT nsid)
    (abi_decode_source_view (vyper_to_abi_type env (StructT nsid)) bs p) v)
Proof
  strip_tac >> drule_all abi_decode_schema_heads_positive >> strip_tac >>
  drule_all abi_decode_positive_head_short_drop >> strip_tac >>
  strip_tac >> drule_all abi_decode_struct_source_head_bound >>
  strip_tac >>
  `LENGTH (abi_decode_source_view (vyper_to_abi_type env (StructT nsid)) bs p)
    <= LENGTH (DROP p bs)` by irule abi_decode_source_view_length_le >> decide_tac
QED

Theorem abi_decode_assignable_tuple_short_head_reject:
  abi_tuple_rows_schema ce env rows /\ assignable_type env (TupleT tys) /\
  tys = MAP (\(ei,ty,tv,asz,msz). ty) rows /\
  LENGTH bs < p + SUM (MAP abi_tuple_row_abi_width rows) ==>
  ~(?v. abi_decode_source_accepts env (TupleT tys)
    (abi_decode_source_view (vyper_to_abi_type env (TupleT tys)) bs p) v)
Proof
  strip_tac >> irule abi_decode_tuple_short_head_reject >>
  qexistsl_tac [`ce`, `rows`] >> simp[] >>
  Cases_on `rows` >> gvs[assignable_type_def]
QED

Theorem abi_decode_assignable_struct_short_head_reject:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  abi_tuple_rows_schema ce (env \\ nsid) rows /\ assignable_type env (StructT nsid) /\
  MAP SND args = MAP (\(ei,ty,tv,asz,msz). ty) rows /\
  LENGTH bs < p + SUM (MAP abi_tuple_row_abi_width rows) ==>
  ~(?v. abi_decode_source_accepts env (StructT nsid)
    (abi_decode_source_view (vyper_to_abi_type env (StructT nsid)) bs p) v)
Proof
  strip_tac >> irule abi_decode_struct_short_head_reject >>
  qexistsl_tac [`args`, `ce`, `rows`] >> simp[] >>
  Cases_on `rows` >> gvs[assignable_type_def]
QED

Theorem abi_decode_tuple_source_value_shape:
  abi_decode_source_accepts env (TupleT tys) view v ==>
  ?vs. v = ArrayV (TupleV vs)
Proof
  simp_tac (srw_ss()) [abi_decode_source_accepts_def, vyper_to_abi_type_def,
    Once dec_def, abi_decode_members_value, abi_to_vyper_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem abi_decode_struct_source_value_shape:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  abi_decode_source_accepts env (StructT nsid) view v ==>
  ?vs. v = StructV (ZIP (MAP FST args,vs))
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_source_accepts _ _ _ _` mp_tac >>
  asm_simp_tac (srw_ss()) [abi_decode_source_accepts_def, vyper_to_abi_type_def,
    Once dec_def, abi_decode_members_value, abi_to_vyper_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem abi_decode_tuple_rows_raw_accept:
  abi_tuple_rows_schema ce env rows /\
  tys = MAP (\(ei,ty,tv,asz,msz). ty) rows /\
  SUM (MAP abi_tuple_row_abi_width rows) <= LENGTH view /\
  LENGTH rows < dimword(:256) ==>
  (abi_decode_source_accepts env (TupleT tys) view v <=>
    ?vs. v = ArrayV (TupleV vs) /\ abi_tuple_rows_accept env view 0 rows vs)
Proof
  strip_tac >> eq_tac
  >- (strip_tac >> drule abi_decode_tuple_source_value_shape >> strip_tac >>
      gvs[] >> metis_tac[abi_tuple_rows_tuple_source]) >>
  strip_tac >> gvs[] >> metis_tac[abi_tuple_rows_tuple_source]
QED

Theorem abi_decode_struct_rows_raw_accept:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  abi_tuple_rows_schema ce (env \\ nsid) rows /\
  MAP SND args = MAP (\(ei,ty,tv,asz,msz). ty) rows /\
  SUM (MAP abi_tuple_row_abi_width rows) <= LENGTH view /\
  LENGTH rows < dimword(:256) ==>
  (abi_decode_source_accepts env (StructT nsid) view v <=>
    ?vs. v = StructV (ZIP (MAP FST args,vs)) /\
      abi_tuple_rows_accept (env \\ nsid) view 0 rows vs)
Proof
  strip_tac >> eq_tac
  >- (strip_tac >> drule_all abi_decode_struct_source_value_shape >> strip_tac >>
      gvs[] >> metis_tac[abi_tuple_rows_struct_source]) >>
  strip_tac >> gvs[] >> metis_tac[abi_tuple_rows_struct_source]
QED


Theorem abi_decode_static_members_valid_take:
  !ts b1 b2 hds. EVERY (\at. ~is_dynamic at) ts ==>
  (vyper_decode_valid_enc_tuple ts b1 (TAKE (SUM (MAP static_length ts)) hds) <=>
   vyper_decode_valid_enc_tuple ts b2 hds)
Proof
  Induct >- simp[vyper_decode_valid_enc_def] >>
  rpt gen_tac >> simp_tac bool_ss [EVERY_DEF] >> strip_tac >>
  asm_simp_tac (srw_ss()) [vyper_decode_valid_enc_def, LET_THM,
    TAKE_TAKE_MIN, DROP_TAKE, LENGTH_TAKE_EQ, MIN_DEF] >>
  Cases_on `static_length h + SUM (MAP static_length ts) <= LENGTH hds` >> simp[] >>
  first_x_assum (qspecl_then [`b1`, `b2`, `DROP (static_length h) hds`] mp_tac) >>
  simp[]
QED

Theorem abi_decode_static_members_decode_take:
  !ts b1 b2 hds. EVERY (\at. ~is_dynamic at) ts ==>
  abi_decode_members ts b1 (TAKE (SUM (MAP static_length ts)) hds) =
  abi_decode_members ts b2 hds
Proof
  Induct >- simp[abi_decode_members_def] >>
  rpt gen_tac >> simp_tac bool_ss [EVERY_DEF] >> strip_tac >>
  asm_simp_tac (srw_ss()) [abi_decode_members_def, abi_decode_member_bytes_def,
    abi_member_head_size_def, TAKE_TAKE_MIN, DROP_TAKE, MIN_DEF] >>
  first_x_assum (qspecl_then [`b1`, `b2`, `DROP (static_length h) hds`] mp_tac) >>
  simp[]
QED

Theorem abi_decode_static_tuple_accept_take:
  EVERY (\at. ~is_dynamic at) (MAP (vyper_to_abi_type env) tys) ==>
  (abi_decode_source_accepts env (TupleT tys)
    (TAKE (SUM (MAP static_length (MAP (vyper_to_abi_type env) tys))) view) v <=>
   abi_decode_source_accepts env (TupleT tys) view v)
Proof
  strip_tac >>
  simp_tac (srw_ss()) [abi_decode_source_accepts_def, vyper_to_abi_type_def,
    vyper_to_abi_types_MAP, Once vyper_decode_valid_enc_def, Once dec_def,
    abi_decode_members_value] >>
  qmatch_asmsub_abbrev_tac `EVERY _ ats` >>
  qmatch_goalsub_abbrev_tac `TAKE k view` >>
  `vyper_decode_valid_enc_tuple ats (TAKE k view) (TAKE k view) =
   vyper_decode_valid_enc_tuple ats view view` by
    (simp[Abbr `k`] >> metis_tac[abi_decode_static_members_valid_take]) >>
  `abi_decode_members ats (TAKE k view) (TAKE k view) =
   abi_decode_members ats view view` by
    (simp[Abbr `k`] >> metis_tac[abi_decode_static_members_decode_take]) >>
  asm_simp_tac (srw_ss()) [vyper_decode_valid_enc_def, Abbr `ats`]
QED

Theorem abi_decode_tuple_source_view_accept:
  abi_decode_source_accepts env (TupleT tys)
    (abi_decode_source_view (vyper_to_abi_type env (TupleT tys)) bs p) v <=>
  abi_decode_source_accepts env (TupleT tys) (DROP p bs) v
Proof
  simp_tac bool_ss [abi_decode_source_view_def] >>
  Cases_on `is_dynamic (vyper_to_abi_type env (TupleT tys))` >- simp[] >>
  `EVERY (\at. ~is_dynamic at) (MAP (vyper_to_abi_type env) tys)` by
    (gvs[vyper_to_abi_type_def, vyper_to_abi_types_MAP, is_dynamic_def,
      any_dynamic_EXISTS, EXISTS_MEM, EVERY_MEM] >> metis_tac[]) >>
  asm_simp_tac (srw_ss()) [vyper_to_abi_type_def, vyper_to_abi_types_MAP,
    static_length_Tuple_SUM, abi_decode_static_tuple_accept_take]
QED

Theorem abi_decode_struct_source_view_accept:
  FLOOKUP env nsid = SOME (StructArgs args) ==>
  (abi_decode_source_accepts env (StructT nsid)
    (abi_decode_source_view (vyper_to_abi_type env (StructT nsid)) bs p) v <=>
   abi_decode_source_accepts env (StructT nsid) (DROP p bs) v)
Proof
  strip_tac >>
  simp_tac bool_ss [abi_decode_source_view_def] >>
  Cases_on `is_dynamic (vyper_to_abi_type env (StructT nsid))` >- simp[] >>
  `EVERY (\at. ~is_dynamic at)
    (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args))` by
    (gvs[vyper_to_abi_type_def, vyper_to_abi_types_MAP, is_dynamic_def,
      any_dynamic_EXISTS, EXISTS_MEM, EVERY_MEM] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `EVERY _ ats` >>
  qmatch_goalsub_abbrev_tac `TAKE k (DROP p bs)` >>
  `k = SUM (MAP static_length ats)` by
    simp[Abbr `k`, Abbr `ats`, vyper_to_abi_type_def, vyper_to_abi_types_MAP,
      static_length_Tuple_SUM] >>
  `vyper_decode_valid_enc_tuple ats (TAKE k (DROP p bs)) (TAKE k (DROP p bs)) =
   vyper_decode_valid_enc_tuple ats (DROP p bs) (DROP p bs)` by
    metis_tac[abi_decode_static_members_valid_take] >>
  `abi_decode_members ats (TAKE k (DROP p bs)) (TAKE k (DROP p bs)) =
   abi_decode_members ats (DROP p bs) (DROP p bs)` by
    metis_tac[abi_decode_static_members_decode_take] >>
  asm_simp_tac (srw_ss()) [abi_decode_source_accepts_def, vyper_to_abi_type_def,
    vyper_to_abi_types_MAP, vyper_decode_valid_enc_def, Once dec_def,
    abi_decode_members_value, Abbr `ats`] >> gvs[]
QED

Theorem abi_decode_tuple_rows_view_accept:
  abi_tuple_rows_schema ce env rows /\
  tys = MAP (\(ei,ty,tv,asz,msz). ty) rows /\
  SUM (MAP abi_tuple_row_abi_width rows) <= LENGTH (DROP p bs) /\
  LENGTH rows < dimword(:256) ==>
  (abi_decode_source_accepts env (TupleT tys)
    (abi_decode_source_view (vyper_to_abi_type env (TupleT tys)) bs p) v <=>
    ?vs. v = ArrayV (TupleV vs) /\ abi_tuple_rows_accept env (DROP p bs) 0 rows vs)
Proof
  simp_tac bool_ss [abi_decode_tuple_source_view_accept] >>
  metis_tac[abi_decode_tuple_rows_raw_accept]
QED

Theorem abi_decode_struct_rows_view_accept:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  abi_tuple_rows_schema ce (env \\ nsid) rows /\
  MAP SND args = MAP (\(ei,ty,tv,asz,msz). ty) rows /\
  SUM (MAP abi_tuple_row_abi_width rows) <= LENGTH (DROP p bs) /\
  LENGTH rows < dimword(:256) ==>
  (abi_decode_source_accepts env (StructT nsid)
    (abi_decode_source_view (vyper_to_abi_type env (StructT nsid)) bs p) v <=>
    ?vs. v = StructV (ZIP (MAP FST args,vs)) /\
      abi_tuple_rows_accept (env \\ nsid) (DROP p bs) 0 rows vs)
Proof
  strip_tac >> drule abi_decode_struct_source_view_accept >>
  disch_then (qspecl_then [`v`, `p`, `bs`] assume_tac) >>
  metis_tac[abi_decode_struct_rows_raw_accept]
QED

Theorem abi_decode_coherent_no_zero_array:
  abi_decoder_coherent ce env sf ty tv /\ assignable_type env ty ==>
  !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem
Proof
  strip_tac >> drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  drule_all assignable_type_slot_size_pos >> strip_tac >>
  metis_tac[evaluated_positive_type_excludes_empty_abi_array]
QED

Theorem abi_decode_constructor_rows_exist:
  !tys tvs.
  LIST_REL (abi_decoder_coherent ce env ce.ce_struct_fields) tys tvs /\
  EVERY (assignable_type env) tys /\ EVERY (abi_decode_bytes_widths env) tys ==>
  ?rows. abi_tuple_rows_schema ce env rows /\
    MAP (\(ei,ty,tv,asz,msz). ty) rows = tys /\
    MAP (\(ei,ty,tv,asz,msz). tv) rows = tvs /\
    MAP (\(ei,ty,tv,asz,msz). (ei,asz,msz)) rows =
      abi_decoder_member_infos ce.ce_struct_fields ce tys
Proof
  Induct >- (rpt gen_tac >> simp[] >> strip_tac >>
    simp[abi_tuple_rows_schema_def, abi_decoder_member_infos_def]) >>
  gen_tac >> Cases_on `tvs` >> simp[] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule abi_decoder_coherent_header >> simp_tac bool_ss [abi_decoder_header_def] >>
  strip_tac >>
  qexists_tac `(type_to_abi_dec_info ce.ce_struct_fields ce h,h,h',
    abi_member_head_size (vyper_to_abi_type env h),type_memory_bytes ce h)::rows` >>
  asm_simp_tac (srw_ss()) [abi_tuple_rows_schema_def, abi_decoder_member_infos_def] >>
  conj_tac >- metis_tac[abi_decode_coherent_no_zero_array] >>
  fs[abi_tuple_rows_schema_def]
QED

Theorem abi_decode_schema_rows_layout:
  !rows. abi_tuple_rows_schema ce env rows ==>
  SUM (MAP abi_tuple_row_abi_width rows) =
    SUM (MAP abi_member_head_size
      (MAP (vyper_to_abi_type env) (MAP (\(ei,ty,tv,asz,msz). ty) rows))) /\
  SUM (MAP abi_tuple_row_mem_width rows) =
    type_memory_size_list (MAP (\(ei,ty,tv,asz,msz). tv) rows)
Proof
  Induct >- simp[abi_tuple_row_abi_width_def, type_memory_size_def] >>
  gen_tac >> PairCases_on `h` >>
  simp_tac (srw_ss()) [abi_tuple_rows_schema_def] >> strip_tac >>
  qpat_x_assum `abi_tuple_rows_schema ce env rows ==> _` mp_tac >>
  asm_simp_tac (srw_ss()) [abi_tuple_rows_schema_def,
    abi_tuple_row_abi_width_def, abi_tuple_row_mem_width_def, type_memory_size_def] >>
  metis_tac[]
QED

Theorem abi_decode_tuple_constructor_rows:
  abi_decoder_coherent ce env ce.ce_struct_fields (TupleT tys) atv /\
  assignable_type env (TupleT tys) /\ abi_decode_bytes_widths env (TupleT tys) ==>
  ?rows. abi_tuple_rows_schema ce env rows /\
    MAP (\(ei,ty,tv,asz,msz). ty) rows = tys /\
    atv = TupleTV (MAP (\(ei,ty,tv,asz,msz). tv) rows) /\
    type_to_abi_dec_info ce.ce_struct_fields ce (TupleT tys) =
      DecComplex (EXISTS (is_abi_dynamic ce.ce_struct_fields) tys)
        (MAP (\(ei,ty,tv,asz,msz). (ei,asz,msz)) rows)
Proof
  simp_tac (srw_ss()) [abi_decoder_coherent_tuple_iff, assignable_type_def,
    abi_decode_bytes_widths_def] >> strip_tac >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  drule_all abi_decode_constructor_rows_exist >> strip_tac >>
  qexists_tac `rows` >> simp[abi_decoder_tuple_infos] >> metis_tac[]
QED

Theorem abi_decode_schema_row_count_bound:
  !rows. abi_tuple_rows_schema ce env rows ==>
  LENGTH rows <= SUM (MAP abi_tuple_row_abi_width rows)
Proof
  Induct >- simp[] >> gen_tac >> PairCases_on `h` >>
  simp_tac (srw_ss()) [abi_tuple_rows_schema_def] >> strip_tac >>
  `LENGTH rows <= SUM (MAP abi_tuple_row_abi_width rows)` by
    (first_x_assum irule >> simp[abi_tuple_rows_schema_def]) >>
  drule_all abi_decode_assignable_embedded_head_positive >>
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  simp[abi_tuple_row_abi_width_def] >> decide_tac
QED

Theorem abi_decode_guard_rows_code_contexts:
  abi_decode_complex_head_guard src hi k st = ((),ready) /\
  compile_abi_decode_complex_elems dst src MLOAD base_op hi
    infos 0 0 ready = ((),last) /\
  abi_decode_code_context func fn st last ==>
  fn_has_code st ready fn /\ abi_decode_code_context func fn ready last /\
  cs_extends st ready /\ cs_extends ready last
Proof
  strip_tac >>
  drule abi_decode_complex_head_guard_prefix_shape >> strip_tac >>
  `cs_extends st ready` by
    (irule cs_extends_same_block >> fs[inst_extends_def]) >>
  `cs_extends ready last` by metis_tac[abi_decode_complex_elems_extends] >>
  `fn_has_code st last fn` by fs[abi_decode_code_context_def] >>
  drule_all fragExecTheory.fn_has_code_split >> strip_tac >>
  metis_tac[exprSimAbiDecodeRowCodeTheory.abi_decode_code_context_suffix]
QED

(* The rows precondition is needed only after the head window fits. *)
Theorem abi_decode_guarded_owned_rows_outcome:
  abi_decode_complex_head_guard src hi (SUM(MAP abi_tuple_row_abi_width rows))
    st = ((),ready) /\
  compile_abi_decode_complex_elems dst src MLOAD base_op hi
    (MAP abi_tuple_row_code rows) 0 0 ready = ((),last) /\
  abi_decode_code_context func fn st last /\
  last.cs_next_var <= limit_st.cs_next_var /\
  abi_decode_sites st.cs_next_id last.cs_next_id SUBSET sites /\
  hi <> Lit 0w /\ eval_operand src s = SOME(n2w p) /\
  eval_operand hi s = SOME(n2w(LENGTH bs)) /\
  p < dimword(:256) /\ LENGTH bs < dimword(:256) /\
  SUM(MAP abi_tuple_row_abi_width rows) < dimword(:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var hi /\
  fresh_vars_wrt limit_st s /\ abi_decode_entry st s /\
  (p+SUM(MAP abi_tuple_row_abi_width rows) <= LENGTH bs ==>
    abi_decode_owned_rows_pre ctx func ce env limit_st next scratch sites
      st dst src base_op hi B bs p d 0 0 rows s) ==>
  (LENGTH bs < p+SUM(MAP abi_tuple_row_abi_width rows) /\
    ?u. Dabort ctx fn s Revert_abort u) \/
  (p+SUM(MAP abi_tuple_row_abi_width rows) <= LENGTH bs /\
    ((?t vs. Dreach ctx fn s t /\
      abi_tuple_rows_values env (DROP p bs) 0 0 d rows vs t /\
      fresh_vars_wrt limit_st t /\
      decode_site_effect ctx func next
        (scratch UNION {a | d <= a /\
          a < d+SUM(MAP abi_tuple_row_mem_width rows)}) s t /\
      abi_decode_alloc_progress (abi_decode_sites st.cs_next_id last.cs_next_id) s t /\
      abi_decode_entry last t) \/
    (?u. Dabort ctx fn s Revert_abort u /\
      ~(?vs. abi_tuple_rows_accept env (DROP p bs) 0 rows vs))))
Proof
  strip_tac >> drule_all abi_decode_guard_rows_code_contexts >> strip_tac >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  `ready.cs_next_var <= limit_st.cs_next_var` by
    (`ci_mono ready last` by metis_tac[cj 2 ci_mono_compile_abi_decode, pairTheory.SND] >>
     gvs[ci_mono_def] >> decide_tac) >>
  Cases_on `p+SUM(MAP abi_tuple_row_abi_width rows) <= LENGTH bs`
  >- suspend "head_fits" >>
  disj1_tac >> conj_tac >- decide_tac >>
  `LENGTH bs < p+SUM(MAP abi_tuple_row_abi_width rows)` by decide_tac >>
  fs[abi_decode_entry_def] >>
  drule_all abi_decode_complex_head_guard_abort_reentry >> simp[]
QED

Resume abi_decode_guarded_owned_rows_outcome[head_fits]:
  `abi_decode_owned_rows_pre ctx func ce env limit_st next scratch sites
    st dst src base_op hi B bs p d 0 0 rows s` by metis_tac[] >>
  `decode_site_resources ctx func s /\ next <= st.cs_next_var` by
    fs[exprSimAbiDecodeOwnedRowsTheory.abi_decode_owned_rows_pre_def] >>
  drule_all abi_decode_complex_head_guard_reach_reentry >>
  disch_then (qspecl_then
    [`scratch UNION {a | d <= a /\ a < d+SUM(MAP abi_tuple_row_mem_width rows)}`,
     `abi_decode_sites st.cs_next_id last.cs_next_id`]
    strip_assume_tac) >>
  `decode_site_resources ctx func t` by metis_tac[decode_site_effect_resources] >>
  `st.cs_next_var <= ready.cs_next_var` by simp[] >>
  drule_all abi_decode_owned_rows_address_frame >> strip_tac >>
  `abi_decode_sites ready.cs_next_id last.cs_next_id SUBSET sites` by
    (irule pred_setTheory.SUBSET_TRANS >>
     qexists_tac `abi_decode_sites st.cs_next_id last.cs_next_id` >>
     fs[abi_decode_sites_def, pred_setTheory.SUBSET_DEF] >>
     drule abi_decode_complex_head_guard_shape >> strip_tac >> decide_tac) >>
  drule_all abi_decode_owned_rows_conditional_outcome >>
  reverse strip_tac
  >- (disj2_tac >> simp[] >> disj2_tac >>
      metis_tac[Dreach_abort]) >>
  `abi_decode_sites ready.cs_next_id last.cs_next_id SUBSET
     abi_decode_sites st.cs_next_id last.cs_next_id` by
    (drule abi_decode_complex_head_guard_shape >>
     simp[abi_decode_sites_def, pred_setTheory.SUBSET_DEF] >>
     rpt strip_tac >> decide_tac) >>
  `abi_decode_alloc_progress (abi_decode_sites st.cs_next_id last.cs_next_id) t t'` by
    metis_tac[abi_decode_alloc_progress_widen] >>
  `decode_site_effect ctx func next
    (scratch UNION {a | d <= a /\ a < d+SUM(MAP abi_tuple_row_mem_width rows)}) s t` by
    metis_tac[decode_site_effect_threshold] >>
  disj2_tac >> simp[] >> disj1_tac >> qexistsl_tac [`t'`,`vs`] >>
  simp[] >> conj_tac >- metis_tac[Dreach_trans] >>
  conj_tac >- (fs[] >> metis_tac[decode_site_effect_trans, pred_setTheory.UNION_IDEMPOT]) >>
  irule abi_decode_alloc_progress_trans >> qexists_tac `t` >> simp[]
QED
Finalise abi_decode_guarded_owned_rows_outcome

(* This boundary intentionally does not discharge the child schema or the
   agreement between descended and full-map descriptors. Those are separate
   obligations of recursive closure, not consequences of layout transport. *)
Theorem abi_decode_struct_constructor_rows_conditional:
  FLOOKUP ce.ce_struct_fields (nsid_to_string nsid) = SOME fields /\
  abi_tuple_rows_schema ce (env \\ nsid) rows /\
  MAP (\(ei,ty,tv,asz,msz). (ei,asz,msz)) rows =
    abi_decoder_member_infos (ce.ce_struct_fields \\ nsid_to_string nsid)
      ce (MAP (FST o SND) fields) ==>
  type_to_abi_dec_info ce.ce_struct_fields ce (StructT nsid) =
    DecComplex (EXISTS (is_abi_dynamic ce.ce_struct_fields)
      (MAP (FST o SND) fields))
      (MAP (\(ei,ty,tv,asz,msz). (ei,asz,msz)) rows)
Proof
  strip_tac >> drule abi_decoder_struct_infos >> simp[]
QED

Theorem abi_decode_constructor_rows_pre:
  abi_tuple_rows_schema ce env rows /\
  EVERY (\(ei,ty,tv,asz,msz). abi_decode_owned_child_contract ce env ty tv) rows /\
  SUM(MAP abi_tuple_row_mem_width rows) = type_memory_bytes ce ty /\
  abi_decode_owned sites scratch d (type_memory_bytes ce ty) s /\
  abi_decode_context_pre ctx func ce parent_env ty tv limit_st next
    (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce ty}) sites
    st dst src base_op hi B bs p d s /\
  p+SUM(MAP abi_tuple_row_abi_width rows) <= LENGTH bs ==>
  abi_decode_owned_rows_pre ctx func ce env limit_st next scratch sites
    st dst src base_op hi B bs p d 0 0 rows s
Proof
  simp_tac bool_ss [abi_decode_context_pre_def,
    exprSimAbiDecodeOwnedRowsTheory.abi_decode_owned_rows_pre_def] >>
  rpt strip_tac >> simp[] >>
  fs[pred_setTheory.IN_UNION] >> metis_tac[]
QED

Theorem abi_decode_tuple_owned_contract_rows:
  abi_tuple_rows_schema ce env rows /\
  tys = MAP (\(ei,ty,tv,asz,msz). ty) rows /\
  atv = TupleTV (MAP (\(ei,ty,tv,asz,msz). tv) rows) /\
  type_to_abi_dec_info ce.ce_struct_fields ce (TupleT tys) =
    DecComplex dyn (MAP abi_tuple_row_code rows) /\
  SUM(MAP abi_tuple_row_mem_width rows) = type_memory_bytes ce (TupleT tys) /\
  SUM(MAP abi_tuple_row_abi_width rows) <= SUM(MAP abi_tuple_row_mem_width rows) /\
  EVERY (\(ei,ty,tv,asz,msz). abi_decode_owned_child_contract ce env ty tv) rows ==>
  abi_decode_owned_child_contract ce env (TupleT tys) atv
Proof
  strip_tac >> simp_tac bool_ss [exprSimAbiDecodeOwnedContextTheory.abi_decode_owned_child_contract_def] >>
  rpt gen_tac >> strip_tac >>
  `assignable_type env (TupleT tys)` by fs[abi_decode_context_pre_def] >>
  `hi <> Lit 0w /\ eval_operand src s = SOME(n2w pos) /\
    eval_operand hi s = SOME(n2w(LENGTH bs)) /\ pos < dimword(:256) /\
    LENGTH bs < dimword(:256) /\
    SUM(MAP abi_tuple_row_abi_width rows) < dimword(:256) /\
    abi_decoder_operand_live st.cs_next_var src /\
    abi_decoder_operand_live st.cs_next_var hi /\
    fresh_vars_wrt limit_st s /\ abi_decode_entry st s` by
    (fs[abi_decode_context_pre_def, EVERY_DEF] >> decide_tac) >>
  `FOLDR (\(_,asz,_) acc. asz+acc) 0 (MAP abi_tuple_row_code rows) =
    SUM(MAP abi_tuple_row_abi_width rows)` by
    (POP_ASSUM_LIST (K ALL_TAC) >> Induct_on `rows` >- simp[] >>
     gen_tac >> PairCases_on `h` >>
     asm_simp_tac (srw_ss()) [MAP, FOLDR, SUM,
       abi_tuple_row_code_def, abi_tuple_row_abi_width_def]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_complex_phases, comp_ignore_bind_def, comp_bind_def] >>
  Cases_on `abi_decode_complex_head_guard src hi
    (SUM(MAP abi_tuple_row_abi_width rows)) st` >>
  rename1 `abi_decode_complex_head_guard src hi _ st = (u,ready)` >>
  Cases_on `u` >> asm_simp_tac bool_ss [] >> strip_tac >>
  `pos+SUM(MAP abi_tuple_row_abi_width rows) <= LENGTH bs ==>
    abi_decode_owned_rows_pre ctx func ce env limit_st next scratch sites
      st dst src base_op hi B bs pos d 0 0 rows s` by
    (strip_tac >> irule abi_decode_constructor_rows_pre >>
     asm_simp_tac bool_ss [] >> qexistsl_tac [`env`,`atv`,`TupleT tys`] >> simp[]) >>
  qpat_x_assum `LET _ _ = ((),last)` mp_tac >>
  qpat_assum `FOLDR _ _ _ = _` (fn th => pure_rewrite_tac [th]) >>
  qpat_assum `abi_decode_complex_head_guard _ _ _ _ = _`
    (fn th => pure_rewrite_tac [th, LET_THM, pairTheory.UNCURRY_DEF]) >>
  BETA_TAC >> strip_tac >>
  drule_all abi_decode_guarded_owned_rows_outcome >>
  strip_tac
  >- (simp_tac bool_ss [abi_decode_context_result_def] >> disj2_tac >>
      metis_tac[abi_decode_assignable_tuple_short_head_reject])
  >- suspend "tuple_accept"
  >> suspend "tuple_reject"
QED
Resume abi_decode_tuple_owned_contract_rows[tuple_accept]:

  `SUM(MAP abi_tuple_row_abi_width rows) <= LENGTH(DROP pos bs) /\
    LENGTH rows < dimword(:256)` by
    (drule abi_decode_schema_row_count_bound >> simp[LENGTH_DROP] >> decide_tac) >>
  `!v. abi_decode_source_accepts env (TupleT tys)
    (abi_decode_source_view (vyper_to_abi_type env (TupleT tys)) bs pos) v <=>
    ?vs. v = ArrayV (TupleV vs) /\ abi_tuple_rows_accept env (DROP pos bs) 0 rows vs` by
    (gen_tac >> metis_tac[abi_decode_tuple_rows_view_accept]) >>
  `abi_tuple_rows_accept env (DROP pos bs) 0 rows vs` by
    metis_tac[abi_tuple_rows_values_accept] >>
  `val_in_memory (TupleTV (MAP (\(ei,ty,tv,asz,msz). tv) rows))
    (ArrayV (TupleV vs)) d t.vs_memory` by
    metis_tac[abi_tuple_rows_tuple_memory] >>
  simp_tac bool_ss [abi_decode_context_result_def] >> disj1_tac >>
  qexistsl_tac [`t`,`ArrayV (TupleV vs)`] >> fs[] >>
  conj_tac >- metis_tac[] >> metis_tac[]
QED
Resume abi_decode_tuple_owned_contract_rows[tuple_reject]:
  `SUM(MAP abi_tuple_row_abi_width rows) <= LENGTH(DROP pos bs) /\
    LENGTH rows < dimword(:256)` by
    (drule abi_decode_schema_row_count_bound >> simp[LENGTH_DROP] >> decide_tac) >>
  `!v. abi_decode_source_accepts env (TupleT tys)
    (abi_decode_source_view (vyper_to_abi_type env (TupleT tys)) bs pos) v <=>
    ?vs. v = ArrayV (TupleV vs) /\ abi_tuple_rows_accept env (DROP pos bs) 0 rows vs` by
    (gen_tac >> metis_tac[abi_decode_tuple_rows_view_accept]) >>
  simp_tac bool_ss [abi_decode_context_result_def] >> disj2_tac >>
  qexists_tac `u` >> metis_tac[]
QED
Finalise abi_decode_tuple_owned_contract_rows

Theorem abi_decode_struct_owned_contract_rows:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  FLOOKUP ce.ce_struct_fields (nsid_to_string nsid) = SOME fields /\
  args = MAP (\(name,ty,sz). (name,ty)) fields /\
  abi_tuple_rows_schema ce (env \\ nsid) rows /\
  MAP (\(ei,ty,tv,asz,msz). ty) rows = MAP (FST o SND) fields /\
  atv = StructTV (ZIP (MAP FST args,MAP (\(ei,ty,tv,asz,msz). tv) rows)) /\
  MAP abi_tuple_row_code rows = abi_decoder_member_infos
    (ce.ce_struct_fields \\ nsid_to_string nsid) ce (MAP (FST o SND) fields) /\
  SUM(MAP abi_tuple_row_abi_width rows) <= SUM(MAP abi_tuple_row_mem_width rows) /\
  EVERY (\(ei,ty,tv,asz,msz). abi_decode_owned_child_contract ce (env \\ nsid) ty tv) rows ==>
  abi_decode_owned_child_contract ce env (StructT nsid) atv
Proof
  strip_tac >> simp_tac bool_ss [exprSimAbiDecodeOwnedContextTheory.abi_decode_owned_child_contract_def] >>
  rpt gen_tac >> strip_tac >>
  `abi_decoder_coherent ce env ce.ce_struct_fields (StructT nsid) atv /\
    assignable_type env (StructT nsid)` by fs[abi_decode_context_pre_def] >>
  `MAP SND args = MAP (\(ei,ty,tv,asz,msz). ty) rows /\
    LENGTH args = LENGTH rows` by
    (conj_asm1_tac
     >- (asm_simp_tac bool_ss [MAP_MAP_o] >>
         irule MAP_CONG >> simp[] >> rpt strip_tac >> PairCases_on `x` >> simp[]) >>
     metis_tac[LENGTH_MAP]) >>
  `SUM(MAP abi_tuple_row_mem_width rows) = type_memory_bytes ce (StructT nsid)` by
    (drule abi_decode_schema_rows_layout >> strip_tac >>
     drule abi_decoder_coherent_header >>
     simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
     `type_memory_size_fields (ZIP (MAP FST args,
       MAP (\(ei,ty,tv,asz,msz). tv) rows)) =
       type_memory_size_list (MAP (\(ei,ty,tv,asz,msz). tv) rows)` by
       (irule type_memory_size_fields_zip >> simp[]) >>
     gvs[type_memory_size_def]) >>
  `type_to_abi_dec_info ce.ce_struct_fields ce (StructT nsid) =
    DecComplex (EXISTS (is_abi_dynamic ce.ce_struct_fields) (MAP (FST o SND) fields))
      (MAP abi_tuple_row_code rows)` by
    (drule abi_decoder_struct_infos >> simp[]) >>
  `hi <> Lit 0w /\ eval_operand src s = SOME(n2w pos) /\
    eval_operand hi s = SOME(n2w(LENGTH bs)) /\ pos < dimword(:256) /\
    LENGTH bs < dimword(:256) /\
    SUM(MAP abi_tuple_row_abi_width rows) < dimword(:256) /\
    abi_decoder_operand_live st.cs_next_var src /\
    abi_decoder_operand_live st.cs_next_var hi /\
    fresh_vars_wrt limit_st s /\ abi_decode_entry st s` by
    (fs[abi_decode_context_pre_def, EVERY_DEF] >> decide_tac) >>
  `FOLDR (\(_,asz,_) acc. asz+acc) 0 (MAP abi_tuple_row_code rows) =
    SUM(MAP abi_tuple_row_abi_width rows)` by
    (POP_ASSUM_LIST (K ALL_TAC) >> Induct_on `rows` >- simp[] >>
     gen_tac >> PairCases_on `h` >>
     asm_simp_tac (srw_ss()) [MAP, FOLDR, SUM,
       abi_tuple_row_code_def, abi_tuple_row_abi_width_def]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_complex_phases, comp_ignore_bind_def, comp_bind_def] >>
  Cases_on `abi_decode_complex_head_guard src hi
    (SUM(MAP abi_tuple_row_abi_width rows)) st` >>
  rename1 `abi_decode_complex_head_guard src hi _ st = (u,ready)` >>
  Cases_on `u` >> asm_simp_tac bool_ss [] >> strip_tac >>
  `pos+SUM(MAP abi_tuple_row_abi_width rows) <= LENGTH bs ==>
    abi_decode_owned_rows_pre ctx func ce (env \\ nsid) limit_st next scratch sites
      st dst src base_op hi B bs pos d 0 0 rows s` by
    (strip_tac >> irule abi_decode_constructor_rows_pre >>
     asm_simp_tac bool_ss [] >> qexistsl_tac [`env`,`atv`,`StructT nsid`] >> simp[]) >>
  qpat_x_assum `LET _ _ = ((),last)` mp_tac >>
  qpat_assum `MAP abi_tuple_row_code rows = _`
    (fn th => pure_rewrite_tac [GSYM th]) >>
  qpat_assum `FOLDR _ _ _ = _` (fn th => pure_rewrite_tac [th]) >>
  qpat_assum `abi_decode_complex_head_guard _ _ _ _ = _`
    (fn th => pure_rewrite_tac [th, LET_THM, pairTheory.UNCURRY_DEF]) >>
  BETA_TAC >> strip_tac >>
  drule_all abi_decode_guarded_owned_rows_outcome >>
  strip_tac
  >- (simp_tac bool_ss [abi_decode_context_result_def] >> disj2_tac >>
      metis_tac[abi_decode_assignable_struct_short_head_reject])
  >- suspend "struct_accept"
  >> suspend "struct_reject"
QED
Resume abi_decode_struct_owned_contract_rows[struct_accept]:
  `SUM(MAP abi_tuple_row_abi_width rows) <= LENGTH(DROP pos bs) /\
    LENGTH rows < dimword(:256)` by
    (drule abi_decode_schema_row_count_bound >> simp[LENGTH_DROP] >> decide_tac) >>
  `!v. abi_decode_source_accepts env (StructT nsid)
    (abi_decode_source_view (vyper_to_abi_type env (StructT nsid)) bs pos) v <=>
    ?vs. v = StructV (ZIP (MAP FST args,vs)) /\
      abi_tuple_rows_accept (env \\ nsid) (DROP pos bs) 0 rows vs` by
    (gen_tac >> metis_tac[abi_decode_struct_rows_view_accept]) >>
  `abi_tuple_rows_accept (env \\ nsid) (DROP pos bs) 0 rows vs` by
    metis_tac[abi_tuple_rows_values_accept] >>
  `val_in_memory atv (StructV (ZIP (MAP FST args,vs))) d t.vs_memory` by
    (`LENGTH(MAP FST args) = LENGTH rows` by simp[] >>
     drule_all abi_tuple_rows_struct_memory >> simp[]) >>
  simp_tac bool_ss [abi_decode_context_result_def] >> disj1_tac >>
  qexistsl_tac [`t`,`StructV (ZIP (MAP FST args,vs))`] >>
  simp_tac bool_ss [] >> metis_tac[]
QED
Resume abi_decode_struct_owned_contract_rows[struct_reject]:
  `SUM(MAP abi_tuple_row_abi_width rows) <= LENGTH(DROP pos bs) /\
    LENGTH rows < dimword(:256)` by
    (drule abi_decode_schema_row_count_bound >> simp[LENGTH_DROP] >> decide_tac) >>
  `!v. abi_decode_source_accepts env (StructT nsid)
    (abi_decode_source_view (vyper_to_abi_type env (StructT nsid)) bs pos) v <=>
    ?vs. v = StructV (ZIP (MAP FST args,vs)) /\
      abi_tuple_rows_accept (env \\ nsid) (DROP pos bs) 0 rows vs` by
    (gen_tac >> metis_tac[abi_decode_struct_rows_view_accept]) >>
  simp_tac bool_ss [abi_decode_context_result_def] >> disj2_tac >>
  qexists_tac `u` >> metis_tac[]
QED
Finalise abi_decode_struct_owned_contract_rows

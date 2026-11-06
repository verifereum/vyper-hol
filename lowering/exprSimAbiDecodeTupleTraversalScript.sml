Theory exprSimAbiDecodeTupleTraversal
Ancestors
  exprSimAbiDecodeOwnedRows exprSimAbiDecodeRowsTransport
  exprSimAbiDecodeRowCode exprSimAbiDecodeOwnedMember
  exprSimAbiDecodeTupleAssembly exprSimAbiDecodeTupleOutcome
  exprSimAbiDecodeMemberExecute exprSimAbiDecodeSiteProvenance
  abiDecoderFiniteControl abiDecoderSiteEffect abiDecoderCoherence abiDecoderOffset
  compileEnv exprLoweringProps venomState vyperABI contractABI
  words list arithmetic pred_set

Theorem abi_decode_owned_rows_conditional_outcome:
  !rows ctx func ce env limit_st next scratch sites st dst src base_op hi
    B bs p d ao vo s last fn.
  abi_decode_owned_rows_pre ctx func ce env limit_st next scratch sites
    st dst src base_op hi B bs p d ao vo rows s /\
  compile_abi_decode_complex_elems dst src MLOAD base_op hi
    (MAP abi_tuple_row_code rows) ao vo st = ((),last) /\
  abi_decode_code_context func fn st last /\
  last.cs_next_var <= limit_st.cs_next_var /\
  abi_decode_sites st.cs_next_id last.cs_next_id SUBSET sites ==>
  (?t vs. Dreach ctx fn s t /\
    abi_tuple_rows_values env (DROP p bs) ao vo d rows vs t /\
    fresh_vars_wrt limit_st t /\
    decode_site_effect ctx func next
      (scratch UNION {a | d+vo <= a /\
        a < d+vo+SUM(MAP abi_tuple_row_mem_width rows)}) s t /\
    abi_decode_alloc_progress (abi_decode_sites st.cs_next_id last.cs_next_id) s t /\
    abi_decode_entry last t) \/
  (?u. Dabort ctx fn s Revert_abort u /\
    ~(?vs. abi_tuple_rows_accept env (DROP p bs) ao rows vs))
Proof
  Induct >-
    (rpt strip_tac >>
     gvs[abi_decode_complex_elems_nil] >> disj1_tac >>
     qexistsl_tac [`s`,`[]`] >>
     fs[abi_decode_owned_rows_pre_def, abi_tuple_rows_values_def,
        Dreach_refl, abi_decode_alloc_progress_refl, decode_site_effect_refl]) >>
  gen_tac >> PairCases_on `h` >> rpt strip_tac >>
  `next <= st.cs_next_var` by
    metis_tac[abi_decode_owned_rows_pre_def] >>
  drule_all abi_decode_mapped_rows_code_split >> strip_tac >>
  `ci_mono st child_end` by (fs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `child_end.cs_next_var <= limit_st.cs_next_var` by
    (fs[ci_mono_def] >> decide_tac) >>
  `abi_decode_sites st.cs_next_id child_end.cs_next_id SUBSET sites` by
    metis_tac[SUBSET_TRANS] >>
  `abi_decode_owned_child_contract ce env h1 h2` by
    metis_tac[abi_decode_owned_rows_head_contract] >>
  `abi_decode_owned sites scratch (d+vo) (type_memory_bytes ce h1) s` by
    metis_tac[abi_decode_owned_rows_head_owned] >>
  `abi_decode_owned_rows_pre ctx func ce env limit_st st.cs_next_var scratch sites
    st dst src base_op hi B bs p d ao vo ((h0,h1,h2,h3,h4)::rows) s` by
    (qhdtm_assum `abi_decode_owned_rows_pre` mp_tac >>
     simp_tac bool_ss [abi_decode_owned_rows_pre_def] >> metis_tac[LESS_EQ_REFL]) >>
  drule abi_decode_owned_rows_head_pre >> strip_tac >>
  `h0 = type_to_abi_dec_info ce.ce_struct_fields ce h1 /\
   dec_info_needs_offset h0 = is_dynamic (vyper_to_abi_type env h1)` by
    (qhdtm_assum `abi_decode_owned_rows_pre` mp_tac >>
     simp_tac (srw_ss()) [abi_decode_owned_rows_pre_def, abi_tuple_rows_schema_def] >>
     rpt strip_tac >> simp[] >> irule abi_decoder_nonempty_type_offset >>
     metis_tac[]) >>
  qpat_x_assum `h0 = _` SUBST_ALL_TAC >>
  qpat_x_assum `dec_info_needs_offset _ = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  drule_all abi_decode_owned_member_conditional_outcome >>
  simp_tac bool_ss [abi_decode_context_result_def] >> reverse strip_tac
  >- (disj2_tac >> qexists_tac `u` >> simp[] >>
      fs[abi_tuple_rows_accept_def, abi_tuple_row_accepts_def,
         abi_decode_source_accepts_def] >> metis_tac[]) >>
  suspend "accepted_head"
QED

Resume abi_decode_owned_rows_conditional_outcome[accepted_head]:
  drule_all abi_decode_owned_rows_suffix >> strip_tac >>
  `abi_decode_sites child_end.cs_next_id last.cs_next_id SUBSET sites` by
    metis_tac[SUBSET_TRANS] >>
  first_x_assum drule_all >> reverse strip_tac
  >- (disj2_tac >> qexists_tac `u` >> conj_tac
      >- metis_tac[Dreach_abort] >>
      fs[abi_tuple_rows_accept_def] >> metis_tac[]) >>
  `abi_tuple_row_accepts env (DROP p bs) ao
    (type_to_abi_dec_info ce.ce_struct_fields ce h1,h1,h2,h3,h4) v` by
    fs[abi_tuple_row_accepts_def, abi_decode_source_accepts_def] >>
  `abi_tuple_rows_schema ce env
    [(type_to_abi_dec_info ce.ce_struct_fields ce h1,h1,h2,h3,h4)]` by
    (qpat_assum `abi_decode_owned_rows_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_::_) _` mp_tac >>
     simp_tac (srw_ss()) [abi_decode_owned_rows_pre_def, abi_tuple_rows_schema_def] >>
     rpt strip_tac >> metis_tac[]) >>
  `val_wf h2 v` by metis_tac[abi_tuple_row_accepts_wf] >>
  `val_in_memory h2 v (d+vo) t'.vs_memory` by
    metis_tac[abi_decode_owned_rows_completed_head] >>
  `h4 = type_memory_bytes ce h1` by
    fs[abi_tuple_rows_schema_def] >>
  `decode_site_effect ctx func st.cs_next_var
    (scratch UNION {a | d+vo <= a /\
      a < d+vo+SUM(MAP abi_tuple_row_mem_width
        ((type_to_abi_dec_info ce.ce_struct_fields ce h1,h1,h2,h3,h4)::rows))}) s t'` by
    (drule_all decode_site_effect_trans >>
     `((scratch UNION {a | d+vo <= a /\ a < d+vo+type_memory_bytes ce h1}) UNION
       (scratch UNION {a | d+(vo+h4) <= a /\
         a < d+(vo+h4)+SUM(MAP abi_tuple_row_mem_width rows)})) =
      (scratch UNION {a | d+vo <= a /\
        a < d+vo+SUM(MAP abi_tuple_row_mem_width
          ((type_to_abi_dec_info ce.ce_struct_fields ce h1,h1,h2,h3,h4)::rows))})` by
       (simp[EXTENSION, abi_tuple_row_mem_width_def] >> gen_tac >>
        Cases_on `x IN scratch` >> simp[] >> decide_tac) >>
     simp[]) >>
  `abi_decode_alloc_progress (abi_decode_sites st.cs_next_id last.cs_next_id) s t` by
    metis_tac[abi_decode_alloc_progress_widen] >>
  `abi_decode_alloc_progress (abi_decode_sites st.cs_next_id last.cs_next_id) t t'` by
    metis_tac[abi_decode_alloc_progress_widen] >>
  disj1_tac >> qexistsl_tac [`t'`,`v::vs`] >>
  conj_tac >- metis_tac[Dreach_trans] >>
  conj_tac >- (simp[abi_tuple_rows_values_def, abi_tuple_row_value_def] >> metis_tac[]) >>
  conj_tac >- simp[] >> conj_tac
  >- (irule decode_site_effect_threshold >> metis_tac[]) >>
  metis_tac[abi_decode_alloc_progress_trans]
QED

Finalise abi_decode_owned_rows_conditional_outcome

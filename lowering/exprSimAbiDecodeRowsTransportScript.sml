Theory exprSimAbiDecodeRowsTransport
Ancestors
  exprSimAbiDecodeOwnedRows exprSimAbiDecodeOwnedContext
  exprSimAbiDecodeTupleAssembly exprSimAbiDecodeTupleOutcome
  exprSimAbiDecodeChildFrame exprSimAbiDecodeSiteProvenance
  abiDecoderSiteEffect abiDecoderFrame abiDecoderContract
  compileEnv exprLoweringProps abiDecoderReentry abiDecoderVarSequence venomState valueEncodingProps finite_map pred_set
  words list arithmetic

Theorem abi_decode_owned_rows_completed_head:
  abi_decode_owned_rows_pre ctx func ce env limit_st next scratch sites
    st dst src base_op hi B bs p d ao vo ((ei,ty,tv,asz,msz)::rows) s /\
  decode_site_effect ctx func next
    (scratch UNION {a | d+(vo+msz) <= a /\
      a < d+(vo+msz)+SUM(MAP abi_tuple_row_mem_width rows)}) t u /\
  val_in_memory tv v (d+vo) t.vs_memory /\ val_wf tv v ==>
  val_in_memory tv v (d+vo) u.vs_memory
Proof
  strip_tac >>
  `decode_protects
    (scratch UNION {a | d+(vo+msz) <= a /\
      a < d+(vo+msz)+SUM(MAP abi_tuple_row_mem_width rows)})
    {(d+vo,type_memory_size tv)}` by
    (fs[abi_decode_owned_rows_pre_def, abi_tuple_rows_schema_def,
        abi_decode_owned_def, abi_tuple_row_mem_width_def,
        decode_protects_def] >> rpt strip_tac >> fs[] >>
     first_x_assum drule >> simp[]) >>
  metis_tac[abi_decode_child_completed_value]
QED

Theorem abi_decode_owned_rows_suffix:
  abi_decode_owned_rows_pre ctx func ce env limit_st next scratch sites
    st dst src base_op hi B bs p d ao vo ((ei,ty,tv,asz,msz)::rows) s /\
  ci_mono st child_end /\ child_end.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st t /\ abi_decode_entry child_end t /\
  decode_site_effect ctx func st.cs_next_var
    (scratch UNION {a | d+vo <= a /\ a < d+vo+type_memory_bytes ce ty}) s t /\
  abi_decode_alloc_progress head_sites s t /\ head_sites SUBSET sites ==>
  abi_decode_owned_rows_pre ctx func ce env limit_st next scratch sites
    child_end dst src base_op hi B bs p d (ao+asz) (vo+msz) rows t
Proof
  strip_tac >>
  `abi_decode_alloc_progress sites s t` by
    metis_tac[abi_decode_alloc_progress_widen] >>
  `decode_protects
    (scratch UNION {a | d+vo <= a /\ a < d+vo+type_memory_bytes ce ty})
    {(B,LENGTH bs)}` by
    (fs[abi_decode_owned_rows_pre_def, abi_tuple_rows_schema_def,
        abi_tuple_row_mem_width_def, abi_footprint_disjoint_def,
        decode_protects_def] >> rpt strip_tac >> fs[] >>
     first_x_assum drule >> simp[]) >>
  `mem_bytes_at B (LENGTH bs) t.vs_memory =
    mem_bytes_at B (LENGTH bs) s.vs_memory` by
    metis_tac[decode_site_effect_protected, IN_SING] >>
  `abi_decode_owned sites scratch (d+vo)
    (SUM(MAP abi_tuple_row_mem_width ((ei,ty,tv,asz,msz)::rows))) t` by
    metis_tac[abi_decode_owned_transport, abi_decode_owned_rows_pre_def] >>
  `abi_decode_owned sites scratch (d+(vo+msz))
    (SUM(MAP abi_tuple_row_mem_width rows)) t` by
    (fs[abi_decode_owned_def, abi_tuple_row_mem_width_def] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  qhdtm_x_assum `abi_decode_owned_rows_pre`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [abi_decode_owned_rows_pre_def, abi_tuple_rows_schema_def,
       abi_tuple_row_mem_width_def, abi_tuple_row_abi_width_def]) >>
  `EVERY (abi_decoder_operand_live child_end.cs_next_var) [dst;src;base_op;hi]` by
    (fs[EVERY_DEF, ci_mono_def] >> metis_tac[abi_decoder_operand_live_mono]) >>
  `eval_operand src t = SOME(n2w p) /\ eval_operand dst t = SOME(n2w d) /\
   eval_operand base_op t = SOME(n2w B) /\ eval_operand hi t = SOME(n2w(LENGTH bs))` by
    (fs[EVERY_DEF] >> metis_tac[decode_site_effect_live]) >>
  `decode_site_resources ctx func t` by metis_tac[decode_site_effect_resources] >>
  `!id b sz. id IN sites /\ FLOOKUP t.vs_allocas id = SOME(b,sz) ==>
    abi_footprint_disjoint B (LENGTH bs) [(b,sz)]` by
    (qpat_assum `abi_decode_alloc_progress sites s t`
       (mp_then Any mp_tac abi_decode_alloc_progress_source_separation) >>
     disch_then (qspecl_then [`LENGTH bs`,`B`] mp_tac) >> metis_tac[]) >>
  simp_tac bool_ss [abi_decode_owned_rows_pre_def] >>
  asm_simp_tac (srw_ss()) [abi_tuple_rows_schema_def] >>
  fs[ci_mono_def, abi_decode_alloc_progress_def, abi_footprint_disjoint_def] >>
  metis_tac[]
QED

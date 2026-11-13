Theory exprSimAbiDecodeOwnedRows
Ancestors
  exprSimAbiDecodeTupleAssembly exprSimAbiDecodeTupleOutcome
  exprSimAbiDecodeOwnedMember exprSimAbiDecodeMemberExecute
  exprSimAbiDecodeSiteProvenance abiDecoderFrame
  exprSimAbiDecodeOwnedContext exprSimAbiDecodeScratchCover
  exprSimAbiDecodeChildBounds abiDecoderCoherence abiValidMembers
  abiDecodeRanges abiDecoderSiteEffect compileEnv venomState
  vyperABI contractABI finite_map pred_set words list arithmetic

Definition abi_decode_owned_rows_pre_def:
  abi_decode_owned_rows_pre ctx func ce env limit_st next scratch sites
    st dst src base_op hi B bs p d ao vo rows s <=>
    abi_tuple_rows_schema ce env rows /\
    EVERY (\(ei,ty,tv,asz,msz). abi_decode_owned_child_contract ce env ty tv) rows /\
    next <= st.cs_next_var /\ st.cs_next_var <= limit_st.cs_next_var /\
    EVERY (abi_decoder_operand_live st.cs_next_var) [dst;src;base_op;hi] /\
    base_op <> Lit 0w /\ hi <> Lit 0w /\
    eval_operand src s = SOME(n2w p) /\ eval_operand dst s = SOME(n2w d) /\
    eval_operand base_op s = SOME(n2w B) /\
    eval_operand hi s = SOME(n2w(LENGTH bs)) /\
    p < dimword(:256) /\ B+LENGTH bs < dimword(:256) /\
    bs = mem_bytes_at B (LENGTH bs) s.vs_memory /\
    B+LENGTH bs <= s.vs_alloca_next /\
    decode_site_resources ctx func s /\ fn_inst_ids_distinct func /\
    fresh_vars_wrt limit_st s /\ abi_decode_entry st s /\
    p+ao+SUM(MAP abi_tuple_row_abi_width rows) <= LENGTH bs /\
    d+vo+SUM(MAP abi_tuple_row_mem_width rows) < dimword(:256) /\
    abi_decode_owned sites scratch (d+vo) (SUM(MAP abi_tuple_row_mem_width rows)) s /\
    abi_footprint_disjoint B (LENGTH bs)
      [(d+vo,SUM(MAP abi_tuple_row_mem_width rows))] /\
    (!a. B <= a /\ a < B+LENGTH bs ==> a NOTIN scratch) /\
    (!id b sz. id IN sites /\ FLOOKUP s.vs_allocas id = SOME(b,sz) ==>
      abi_footprint_disjoint B (LENGTH bs) [(b,sz)])
End

Theorem abi_decode_owned_rows_head_contract:
  abi_decode_owned_rows_pre ctx func ce env limit_st next scratch sites
    st dst src base_op hi B bs p d ao vo ((ei,ty,tv,asz,msz)::rows) s ==>
  abi_decode_owned_child_contract ce env ty tv
Proof
  simp[abi_decode_owned_rows_pre_def]
QED

Theorem abi_decode_owned_rows_head_owned:
  abi_decode_owned_rows_pre ctx func ce env limit_st next scratch sites
    st dst src base_op hi B bs p d ao vo ((ei,ty,tv,asz,msz)::rows) s ==>
  abi_decode_owned sites scratch (d+vo) (type_memory_bytes ce ty) s
Proof
  simp_tac (srw_ss()) [abi_decode_owned_rows_pre_def, abi_tuple_rows_schema_def,
    abi_tuple_row_mem_width_def] >> strip_tac >>
  fs[abi_decode_owned_def]
QED

(* Empty scratch regions do not constrain their base addresses. *)
Theorem abi_decode_empty_site_cover_probe[local]:
  (!a. 10 <= a /\ a < 20 ==> a NOTIN {a:num | 30 <= a}) /\
  {a:num | 15 <= a /\ a < 15+0} SUBSET {a | 30 <= a} /\
  ~abi_footprint_disjoint 10 10 [(15,0)]
Proof
  simp[abiDecoderFrameTheory.abi_footprint_disjoint_def, SUBSET_DEF]
QED

Theorem abi_decode_owned_rows_head_pre:
  abi_decode_owned_rows_pre ctx func ce env limit_st next scratch sites
    st dst src base_op hi B bs p d ao vo ((ei,ty,tv,asz,msz)::rows) s ==>
  abi_decode_member_pre ctx func ce env ty tv limit_st next
    (scratch UNION {a | d+vo <= a /\ a < d+vo+type_memory_bytes ce ty}) sites
    st dst src base_op hi B bs p d ao vo
    (abi_head_word (DROP ao (DROP p bs))) s
Proof
  strip_tac >>
  `abi_decode_owned sites scratch (d+vo) (type_memory_bytes ce ty) s` by
    metis_tac[abi_decode_owned_rows_head_owned] >>
  qhdtm_x_assum `abi_decode_owned_rows_pre`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [abi_decode_owned_rows_pre_def, abi_tuple_rows_schema_def,
       abi_tuple_row_mem_width_def, abi_tuple_row_abi_width_def]) >>
  `abi_decode_site_writes sites (d+vo) (type_memory_bytes ce ty) s SUBSET
    scratch UNION {a | d+vo <= a /\ a < d+vo+type_memory_bytes ce ty}` by
    metis_tac[abi_decode_owned_writes] >>
  `!clamp. type_to_abi_dec_info ce.ce_struct_fields ce ty = DecPrimWord clamp ==>
    p+ao+32 <= LENGTH bs` by
    (rpt strip_tac >> drule_all abi_decode_scalar_member_head >> strip_tac >>
     drule abi_decoder_coherent_header >>
     simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >> fs[]) >>
  `is_dynamic (vyper_to_abi_type env ty) ==> p+ao+32 <= LENGTH bs` by
    (strip_tac >> fs[abi_member_head_size_def]) >>
  simp_tac bool_ss [abi_decode_member_pre_def] >>
  asm_simp_tac (srw_ss()) [] >>
  fs[abiDecoderFrameTheory.abi_footprint_disjoint_def] >>
  metis_tac[]
QED

Theorem abi_decode_alloc_progress_source_separation:
  abi_decode_alloc_progress sites s t /\ B+n <= s.vs_alloca_next /\
  (!id b sz. id IN sites /\ FLOOKUP s.vs_allocas id = SOME(b,sz) ==>
    abi_footprint_disjoint B n [(b,sz)]) ==>
  (!id b sz. id IN sites /\ FLOOKUP t.vs_allocas id = SOME(b,sz) ==>
    abi_footprint_disjoint B n [(b,sz)])
Proof
  simp_tac bool_ss [abi_decode_alloc_progress_def] >> rpt strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas id`
  >- (fs[abiDecoderFrameTheory.abi_footprint_disjoint_def] >>
      metis_tac[LESS_EQ_TRANS]) >>
  PairCases_on `x` >> metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ]
QED

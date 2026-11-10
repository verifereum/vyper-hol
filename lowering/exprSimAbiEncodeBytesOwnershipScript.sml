Theory exprSimAbiEncodeBytesOwnership
Ancestors
  loweringPosts valueEncoding vyperValue vyperContext compileEnv
  venomState words finite_map arithmetic abiBuiltinAllocation
  exprSimAbiEncodePrefixWindow localPtrsProps exprLoweringProps
  abiBuiltinEncodeCode abiBuiltinEncodeContext abiEncoderCounters venomInst

Theorem abi_encode_bytes_vv_holds:
  read_result cx result es' = (INL (BytesV payload),es') /\
  eval_operand out actual = SOME (n2w p) /\ p < dimword (:256) /\
  val_in_memory (BaseTV (BytesT (Dynamic N))) (BytesV payload) p actual.vs_memory ==>
  vv_holds ce cx (BaseT (BytesT (Dynamic N))) result
    (LocatedValue (BaseT (BytesT (Dynamic N)))
      <|ptr_operand := out; ptr_location := LocMemory|>) es' actual
Proof
  rpt strip_tac >> simp[vv_holds_def, evaluate_type_def, is_word_type_def] >>
  qexists_tac `n2w p` >> simp[w2n_n2w] >>
  qexists_tac `BytesV payload` >> simp[]
QED

Theorem abi_encode_bytes_vv_at:
  read_result cx result es' = (INL (BytesV payload),es') /\
  eval_operand out actual = SOME (n2w p) /\ p < dimword (:256) /\
  LENGTH payload <= N /\
  FLOOKUP actual.vs_allocas aid = SOME(p,sz) /\
  origin.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  32+LENGTH payload <= sz /\
  (!name b n. local_region ce es'.scopes actual name b n ==> p+sz <= b \/ b+n <= p) ==>
  vv_at ce cx (BaseT (BytesT (Dynamic N))) origin sb es' result
    (LocatedValue (BaseT (BytesT (Dynamic N)))
      <|ptr_operand := out; ptr_location := LocMemory|>) actual
Proof
  rpt strip_tac >> simp[vv_at_def, evaluate_type_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[] >> conj_tac
  >- (simp[val_wf_def, type_memory_size_def] >>
      qspec_then `N` mp_tac abi_builtin_word_size_capacity >> decide_tac) >>
  disj1_tac >> qexistsl_tac [`aid`, `p`, `sz`] >> simp[val_footprint_def] >> metis_tac[]
QED

Theorem abi_encode_setup_row_local_exclusion:
  abi_builtin_encode_setup mid maxlen sa = (ops,ready) /\
  fn_has_code sa ready func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es' actual /\
  FLOOKUP actual.vs_allocas sa.cs_next_id = SOME(p,sz) ==>
  !name b n. local_region ce es'.scopes actual name b n ==>
    p+sz <= b \/ b+n <= p
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all abi_encode_setup_alloca_code >> strip_tac >>
  `alloca_inv actual /\ local_ptrs_rel func ce es'.scopes actual` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `not_local_ptr ce es'.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (irule local_ptrs_reserved_fresh >> goal_assum (drule_at Any) >> simp[]) >>
  drule_at (Pat `MEM _ (fn_insts _)`) local_ptrs_rel_alloca_disjoint >>
  simp[mk_inst_def] >>
  disch_then drule_all >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def]
QED

Theorem abi_encode_row_local_exclusion:
  lower_abi_encode F mid op ei maxlen sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es' actual /\
  FLOOKUP actual.vs_allocas sa.cs_next_id = SOME(p,sz) ==>
  !name b n. local_region ce es'.scopes actual name b n ==>
    p+sz <= b \/ b+n <= p
Proof
  strip_tac >> drule lower_abi_encode_trace >> strip_tac >>
  drule_all abi_builtin_encode_code >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  drule_all abi_encode_setup_row_local_exclusion >> simp[]
QED

Theorem abi_encode_strict_id_growth:
  lower_abi_encode ensure mid op ei maxlen sa = (out,sb) ==>
  sa.cs_next_id < sb.cs_next_id
Proof
  strip_tac >> drule lower_abi_encode_trace >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  Cases_on `mid` >> gvs[] >> decide_tac
QED

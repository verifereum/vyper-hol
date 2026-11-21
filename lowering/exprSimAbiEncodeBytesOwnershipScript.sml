Theory exprSimAbiEncodeBytesOwnership
Ancestors
  loweringStateRelDefs valueEncodingDefs exprSimProps exprBopSimProps vyperState vyperAST
    loweringPosts valueEncoding vyperValue vyperContext compileEnv
  venomState words finite_map arithmetic abiBuiltinAllocation
  exprSimAbiEncodePrefixWindow localPtrsProps exprLoweringProps
  abiBuiltinEncodeCode abiBuiltinEncodeContext abiEncoderCounters venomInst
  abiBuiltinEncodeSource abiBuiltinEncodeMethod abiBuiltinEncodeRun
  valueEncodingProps vyperTypeSystem context

Theorem abi_encode_bytes_vv_holds:
  read_result cx result es' = (INL (BytesV payload),es') /\
  eval_operand out actual = SOME (n2w p) /\ p < dimword (:256) /\
  val_in_memory (BaseTV (BytesT (Dynamic N))) (BytesV payload) p actual.vs_memory ==>
  vv_holds ce cx (BaseT (BytesT (Dynamic N))) result
    (LocatedValue (BaseT (BytesT (Dynamic N))) (mk_ptr out LocMemory)) es' actual
Proof
  rpt strip_tac >> simp[vv_holds_def, evaluate_type_def, is_word_type_def, mk_ptr_def] >>
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
    (LocatedValue (BaseT (BytesT (Dynamic N))) (mk_ptr out LocMemory)) actual
Proof
  rpt strip_tac >> simp[vv_at_def, evaluate_type_def, mk_ptr_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[] >> conj_tac
  >- (simp[val_wf_def, type_memory_size_def] >>
      qspec_then `N` mp_tac abi_builtin_word_size_capacity >> decide_tac) >>
  disj1_tac >> qexistsl_tac [`aid`, `p`, `sz`] >> simp[val_footprint_def] >> metis_tac[]
QED

Theorem abi_encode_setup_row_local_exclusion:
  abi_builtin_encode_setup mid maxlen sa = (ops,ready) /\
  fn_has_code sa ready func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx es' actual /\
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
  lower_abi_encode mid maxlen
    (\dst. compile_abi_encode_to_buf dst op ei) sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx es' actual /\
  FLOOKUP actual.vs_allocas sa.cs_next_id = SOME(p,sz) ==>
  !name b n. local_region ce es'.scopes actual name b n ==>
    p+sz <= b \/ b+n <= p
Proof
  strip_tac >> drule lower_abi_encode_trace >> BETA_TAC >> strip_tac >>
  drule_all abi_builtin_encode_code >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  drule_all abi_encode_setup_row_local_exclusion >> simp[]
QED

Theorem abi_encode_strict_id_growth:
  lower_abi_encode mid maxlen
    (\dst. compile_abi_encode_to_buf dst op ei) sa = (out,sb) ==>
  sa.cs_next_id < sb.cs_next_id
Proof
  strip_tac >> drule lower_abi_encode_trace >> BETA_TAC >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  Cases_on `mid` >> gvs[] >> decide_tac
QED

Theorem abi_encode_bytes_vv_post:
  expr_type e = BaseT (BytesT (Dynamic N)) /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx es' actual /\
  storage_well_formed_on cx es' (FST H) /\
  read_result cx result es' = (INL (BytesV payload),es') /\
  eval_operand out actual = SOME (n2w p) /\ p < dimword (:256) /\
  LENGTH payload <= N /\
  val_in_memory (BaseTV (BytesT (Dynamic N))) (BytesV payload) p actual.vs_memory /\
  FLOOKUP actual.vs_allocas aid = SOME(p,sz) /\
  origin.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  32+LENGTH payload <= sz /\
  (!name b n. local_region ce es'.scopes actual name b n ==> p+sz <= b \/ b+n <= p) /\
  wb_frame ce es es' origin s0 actual /\
  (~expr_has_effect e ==> pure_frame ce func es origin s0 actual) ==>
  vv_post H ctx func ce cx e es origin sb s0 es' (Value (BytesV payload))
    (LocatedValue (expr_type e) (mk_ptr out LocMemory)) actual
Proof
  strip_tac >>
  `read_result cx (Value (BytesV payload)) es' = (INL (BytesV payload),es')` by
    simp[read_result_def, return_def] >>
  `post_value_type ce e = expr_type e` by
    (irule post_value_type_bytestring >> simp[compileEnvTheory.is_bytestring_type_def]) >>
  simp_tac bool_ss [vv_post_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (simp[] >> irule abi_encode_bytes_vv_holds >>
    goal_assum (drule_at Any) >> simp[] >> qexists_tac `p` >> simp[]) >>
  conj_tac >- (simp[] >> irule abi_encode_bytes_vv_at >>
    goal_assum (drule_at Any) >> simp[] >>
    qexistsl_tac [`aid`, `p`, `sz`] >> fs[] >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
  fs[wb_frame_def] >> simp[mk_ptr_def] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem abi_encode_tuple_result_memory:
  well_typed_type_builtin_args (AbiEncode ensure mid0) target tys /\
  mid = OPTION_MAP bytes_method_id_word mid0 /\
  mload p actual = n2w (LENGTH bytes + (case mid of NONE => 0 | SOME _ => 4)) /\
  mem_bytes_at (p+32+(case mid of NONE => 0 | SOME _ => 4))
    (LENGTH bytes) actual.vs_memory = bytes /\
  (case mid of NONE => T | SOME selector =>
    mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes selector) ==>
  val_in_memory (BaseTV (BytesT (Dynamic N)))
    (BytesV (abi_encode_method_id_bytes mid0 ++ bytes)) p actual.vs_memory
Proof
  strip_tac >> drule abi_builtin_encode_checked_prefix >> strip_tac >>
  Cases_on `mid`
  >- (Cases_on `mid0` >> gvs[abi_builtin_encode_prefix_def,
        abi_encode_method_id_bytes_def, val_in_memory_def, mem_word_at_eq_mload]) >>
  fs[] >> drule_all abi_builtin_encode_method_value >> strip_tac >>
  Cases_on `mid0` >> gvs[abi_builtin_encode_prefix_def,
    abi_encode_method_id_bytes_def, val_in_memory_def, mem_word_at_eq_mload,
    abi_builtin_encode_method_bytes_length]
QED

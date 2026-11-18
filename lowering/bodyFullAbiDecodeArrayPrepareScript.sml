Theory bodyFullAbiDecodeArrayPrepare
Ancestors
  abiEncoderAddressReach[qualified,ignore_grammar]
  abiDecoderDynarrayBound[qualified,ignore_grammar]
  abiDecoderBytesBound[qualified,ignore_grammar]
  bodyFullAbiDecodeGuardReadJoint bodyFullAbiDecodeFiniteObserved
  bodyFullAbiDecodeInputOrigin abiDecoderDynarrayPrefix abiDecoderArrayHeader
  abiDecoderGuards abiDecoderGuard abiDecoderArrayLoopInit
  exprLoweringProps emitHelperProps compileEnv fragExec emitHelper rich_list abiEncoder

Theorem array_prepare_count_extends[local]:
  abi_decode_le_guard cnt bound sa = ((),sb) ==> cs_extends sa sb
Proof
  `abi_decode_le_guard cnt bound sa = ((),sb) ==>
   sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb` by
    (simp[abi_decode_le_guard_def, emit_op_def, emit_void_def, fresh_var_def,
          fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def] >> strip_tac >> gvs[]) >>
  strip_tac >> drule abi_decode_le_guard_shape >>
  simp[inst_extends_def] >> strip_tac >> irule cs_extends_same_block >>
  simp[IS_PREFIX_APPEND]
QED

Theorem array_prepare_payload_extends[local]:
  abi_decode_dynarray_payload_guard head cnt stride hi sa = ((),sb) ==>
  cs_extends sa sb
Proof
  `abi_decode_dynarray_payload_guard head cnt stride hi sa = ((),sb) ==>
   sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb` by
    (simp[abiDecoderDynarrayBoundTheory.abi_decode_dynarray_payload_guard_def,
          compile_abi_decode_range_check_def, emit_op_def, emit_void_def,
          fresh_var_def, fresh_id_def, emit_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >>
     Cases_on `hi = Lit 0w` >> simp[comp_return_def] >> strip_tac >>
     gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def,
         fresh_var_def, fresh_id_def]) >>
  strip_tac >> drule abiDecoderDynarrayBoundTheory.abi_decode_dynarray_payload_guard_shape >>
  simp[inst_extends_def] >> strip_tac >> irule cs_extends_same_block >>
  simp[IS_PREFIX_APPEND]
QED

Theorem array_prepare_trace[local]:
  abi_decode_dynarray_position_prefix src MLOAD (Var input) hi maxn stride
    start = (addr,guard_st) /\
  abi_decode_array_header dst addr MLOAD guard_st = (cnt,header_st) ==>
  ?head head_st addr_st read_st check_st first reload_st.
    abi_decode_bytes_head src hi start = (head,head_st) /\
    compile_abi_dec_addr (Var input) src head_st = (addr,addr_st) /\
    emit_op MLOAD [addr] addr_st = (first,read_st) /\
    abi_decode_le_guard first (Lit (n2w maxn)) read_st = ((),check_st) /\
    abi_decode_dynarray_payload_guard head first stride hi check_st = ((),guard_st) /\
    emit_op MLOAD [addr] guard_st = (cnt,reload_st) /\
    emit_void MSTORE [dst;cnt] reload_st = ((),header_st) /\
    cs_extends start head_st /\ cs_extends head_st addr_st /\
    cs_extends addr_st read_st /\ cs_extends read_st check_st /\
    cs_extends check_st guard_st /\ cs_extends guard_st reload_st /\
    cs_extends reload_st header_st /\
    (!finish obs. cs_extends header_st finish /\ fn_has_code start finish obs ==>
      fn_has_code start head_st obs /\ fn_has_code head_st read_st obs /\
      fn_has_code read_st check_st obs /\ fn_has_code check_st guard_st obs /\
      fn_has_code guard_st reload_st obs /\ fn_has_code reload_st header_st obs)
Proof
  simp[abi_decode_dynarray_position_prefix_trace] >> strip_tac >>
  qpat_x_assum `abi_decode_count_guard _ _ _ _ = _` mp_tac >>
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> pairarg_tac >> strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
  simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> pairarg_tac >> strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `abi_decode_bytes_head src hi start = (head,head_st)` >>
  rename1 `compile_abi_dec_addr (Var input) src head_st = (addr,addr_st)` >>
  rename1 `emit_op MLOAD [addr] addr_st = (first,read_st)` >>
  rename1 `emit_op MLOAD [addr] guard_st = (cnt,reload_st)` >>
  rename1 `emit_void MSTORE [dst;cnt] reload_st = ((),header_st)` >>
  `abi_decode_le_guard first (Lit (n2w maxn)) read_st = ((),count_st)` by
    simp[abi_decode_le_guard_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def] >>
  qexists_tac `count_st` >> asm_rewrite_tac[] >>
  `cs_extends start head_st` by
    (drule abiDecoderBytesBoundTheory.abi_decode_bytes_head_fragment_shape >>
     simp[inst_extends_def] >> strip_tac >> irule cs_extends_same_block >>
     simp[IS_PREFIX_APPEND]) >>
  `emit_op ADD [Var input;src] head_st = (addr,addr_st)` by
    fs[compile_abi_dec_addr_def] >>
  `cs_extends head_st addr_st /\ cs_extends addr_st read_st /\
   cs_extends guard_st reload_st` by
    metis_tac[abiEncoderAddressReachTheory.abi_encoder_emit_address_shape] >>
  drule array_prepare_count_extends >> strip_tac >>
  drule array_prepare_payload_extends >> strip_tac >>
  `cs_extends reload_st header_st` by
    (qspecl_then [`MSTORE`, `[dst;cnt]`, `reload_st`, `K T`]
       mp_tac externalEntryShapeTheory.emit_void_labels >> simp[]) >>
  asm_rewrite_tac[] >> qx_gen_tac `end_st` >> qx_gen_tac `obs` >> strip_tac >>
  `cs_extends head_st read_st` by metis_tac[cs_extends_trans] >>
  MAP_EVERY (fn (a,b) =>
    qspecl_then [a,b,`end_st`] (fn th => mp_tac th >> simp[] >> strip_tac)
      cs_extends_trans)
    [(`reload_st`,`header_st`), (`guard_st`,`reload_st`),
     (`count_st`,`guard_st`), (`read_st`,`count_st`), (`head_st`,`read_st`)] >>
  MAP_EVERY (fn (a,b) =>
    qspecl_then [a,b,`end_st`,`obs`] (fn th => mp_tac th >> simp[] >> strip_tac)
      fn_has_code_split)
    [(`start`,`head_st`), (`head_st`,`read_st`), (`read_st`,`count_st`),
     (`count_st`,`guard_st`), (`guard_st`,`reload_st`), (`reload_st`,`header_st`)] >>
  asm_rewrite_tac[]
QED

(* Arbitrary-input bounded prefix for the unclamped dynamic-array branch. *)
Theory abiMalformedBulkArray
Ancestors
  abiMalformedBytesExecution abiMalformedBulkConstructor abiMalformedRecursiveInterface
  abiMalformedLeafProbe abiMalformedNavigation
  abiMalformedConstructorContract freshWrites venomInst finite_map
  abiDecoderArrayHeader abiDecoderBulk abiDecoderLayout abiDecoderCoherence
  abiDecoderComposition
  venomMemDefs valueEncoding valueEncodingProps
  abiBoundedBytesExecution abiDecoderDynarrayPrefix abiDecoderDynarrayBound
  abiDecoderBytesBound abiDecoderGuards abiDecoderRange abiDecoderContract
  abiEncoder emitHelper emitHelperProps exprLoweringProps compileEnv loweringStateRelDefs
  venomState venomExecSemantics words list rich_list arithmetic

Theorem abi_malformed_dynarray_prefix_total:
  abi_decode_dynarray_position_prefix pos opc base_op hi maxn stride st = (addr,en) /\
  abi_decode_source_opcode opc /\ hi <> Lit 0w /\ maxn < dimword (:256) /\
  maxn * stride < dimword (:256) /\
  eval_operand pos s = SOME (n2w p) /\ p < dimword (:256) /\
  eval_operand base_op s = SOME (n2w b) /\
  eval_operand hi s = SOME (n2w h) /\ h < dimword (:256) /\
  fresh_vars_wrt st s ==>
  (?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t) \/
  (?c t. c <= maxn /\ p + 32 + c * stride <= h /\
    abi_decode_load opc (n2w (b+p) : bytes32) s = n2w c /\
    run_inst_seq (emitted_insts st en) s = OK t /\
    eval_operand addr t = SOME (n2w (b+p)) /\ fresh_vars_wrt en t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st en)
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_dynarray_position_prefix _ _ _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[abi_decode_dynarray_position_prefix_trace] >> strip_tac >>
  drule_all abi_decode_bytes_head_total >> strip_tac
  >- suspend "head_abort" >>
  rename1 `run_inst_seq (emitted_insts st head_st) s = OK s1` >>
  gvs[w2n_n2w, LESS_MOD] >>
  `eval_operand base_op s1 = SOME (n2w b) /\
   eval_operand pos s1 = SOME (n2w p)` by metis_tac[] >>
  drule_all compile_abi_dec_addr_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts head_st addr_st) s1 = OK s2` >>
  `inst_extends head_st addr_st` by
    (Cases_on `base_op = Lit 0w` >>
     gvs[compile_abi_dec_addr_def, comp_return_def, inst_extends_refl] >>
     metis_tac[inst_extends_emit_op]) >>
  `run_inst_seq (emitted_insts st addr_st) s = OK s2 /\
   inst_extends st addr_st` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `head_st`] >> simp[]) >>
  drule_all abi_decode_count_guard_total >> strip_tac
  >- suspend "count_abort" >>
  rename1 `run_inst_seq (emitted_insts addr_st count_st) s2 = OK s3` >>
  `eval_operand head s3 = SOME (n2w (p+32)) /\
   eval_operand hi s3 = SOME (n2w h)` by metis_tac[] >>
  `w2n (abi_decode_load opc (n2w (b+p) : bytes32) s2) * stride < dimword (:256)` by
    (irule LESS_EQ_LESS_TRANS >> qexists_tac `maxn * stride` >> simp[] >> disj2_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand cnt s3 = SOME (n2w (w2n (abi_decode_load opc (n2w (b+p) : bytes32) s2)))` by simp[] >>
  drule_all abi_dynarray_payload_checked_total >> strip_tac
  >- suspend "payload_abort" >>
  suspend "success"
QED

Resume abi_malformed_dynarray_prefix_total[head_abort]:
  disj1_tac >> drule abi_decode_bytes_head_shape >> strip_tac >>
  `inst_extends head_st addr_st` by
    (Cases_on `base_op = Lit 0w` >>
     gvs[compile_abi_dec_addr_def, comp_return_def, inst_extends_refl] >>
     metis_tac[inst_extends_emit_op]) >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  drule abi_decode_dynarray_payload_guard_shape >> strip_tac >>
  `inst_extends head_st en` by metis_tac[inst_extends_trans] >>
  drule_all run_inst_seq_abort_extends >> simp[] >> metis_tac[]
QED

Resume abi_malformed_dynarray_prefix_total[count_abort]:
  disj1_tac >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  drule_all run_inst_seq_emit_extend >> strip_tac >> gvs[] >>
  `inst_extends st count_st` by metis_tac[inst_extends_trans] >>
  drule abi_decode_dynarray_payload_guard_shape >> strip_tac >>
  irule_at Any run_inst_seq_abort_extends >>
  qexists_tac `count_st` >> simp[]
QED

Resume abi_malformed_dynarray_prefix_total[payload_abort]:
  disj1_tac >> drule abi_decode_count_guard_shape >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule abi_decode_dynarray_payload_guard_shape >> strip_tac >>
  drule_all run_inst_seq_emit_extend >> simp[] >> metis_tac[]
QED

Resume abi_malformed_dynarray_prefix_total[success]:
  disj2_tac >>
  `p+32 < dimword (:256)` by decide_tac >>
  `abi_decode_load opc (n2w (b+p) : bytes32) s2 = abi_decode_load opc (n2w (b+p) : bytes32) s` by
    gvs[abi_decode_load_def, abi_decode_source_def, mload_def] >>
  gvs[w2n_n2w, LESS_MOD] >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  drule abi_decode_dynarray_payload_guard_shape >> strip_tac >>
  `run_inst_seq (emitted_insts st count_st) s = OK s3 /\
   inst_extends st count_st` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`, `addr_st`] >> simp[]) >>
  `run_inst_seq (emitted_insts st en) s = OK t /\ inst_extends st en` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s3`, `count_st`] >> simp[]) >>
  qexistsl_tac [`w2n (abi_decode_load opc (n2w (b+p) : bytes32) s)`, `t`] >>
  simp[] >> metis_tac[]
QED

Finalise abi_malformed_dynarray_prefix_total

Theorem abi_malformed_dynarray_prefix_exact:
  abi_decode_dynarray_position_prefix src MLOAD base_op hi maxn stride st = (addr,en) /\
  run_inst_seq (emitted_insts st en) s = OK t ==>
  t = s with vs_vars := t.vs_vars /\
  (!x. not_fresh_at st x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  strip_tac >> irule abi_malformed_read_sequence_frame >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `abi_decode_dynarray_position_prefix _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `hi = Lit 0w` >> Cases_on `base_op = Lit 0w` >>
  simp[abi_decode_dynarray_position_prefix_def, abi_decode_bytes_head_def,
    compile_abi_dec_addr_def, abi_decode_count_guard_def,
    abi_decode_dynarray_payload_guard_def, compile_abi_decode_range_check_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, fresh_write_op_def,
       abi_decode_source_opcode_def, not_fresh_at_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem abi_malformed_bulk_capacity:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray ei abi_sz mem_sz F maxn /\ ~dec_info_needs_clamp ei /\
  type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= outsz /\
  d+outsz < dimword (:256) ==>
  abi_sz = mem_sz /\ maxn < dimword (:256) /\
  maxn * abi_sz < dimword (:256) /\ 32+maxn*mem_sz <= outsz
Proof
  strip_tac >>
  `DecDynArray ei abi_sz mem_sz F maxn =
    type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn))` by simp[] >>
  drule_all abi_decoder_bulk_metadata >> strip_tac >> gvs[] >> decide_tac
QED

Theorem abi_malformed_array_header_exact:
  abi_decode_array_header dst addr MLOAD st = (cnt,en) /\
  eval_operand addr s = SOME a /\ eval_operand dst s = SOME (n2w d) /\
  d < dimword (:256) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st en) s = OK t /\ fresh_vars_wrt en t /\
    eval_operand cnt t = SOME (mload (w2n a) s) /\
    t = (mstore d (mload (w2n a) s) s) with vs_vars := t.vs_vars /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
Proof
  simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MLOAD [addr] st = (cnt,c1)` >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `s1 = s with vs_vars := s1.vs_vars /\
   (!x. not_fresh_at st x ==> lookup_var x s1 = lookup_var x s)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     simp[lookup_var_def] >> irule abi_malformed_read_sequence_frame >>
     goal_assum (drule_at Any) >>
     simp[mk_inst_def, abi_decode_source_opcode_def, not_fresh_at_def]) >>
  `eval_operand dst s1 = SOME (n2w d)` by metis_tac[] >>
  drule_all emit_void_MSTORE_correct >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  drule inst_extends_emit_void >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  gvs[abi_decode_load_def, eval_operand_mstore, w2n_n2w] >>
  qpat_assum `s1 = s with vs_vars := _` SUBST1_TAC >>
  simp_tac std_ss [mstore_def, write_memory_with_expansion_def, LET_THM,
    venom_state_accfupds, venom_state_fupdfupds, venom_state_component_equality]
QED

Theorem abi_malformed_bulk_pointer_sequence:
  emit_op MUL [cnt; Lit (n2w mem_sz)] st = (sz_op,c1) /\
  emit_op ADD [src; Lit 32w] c1 = (src_data,c2) /\
  compile_abi_dec_addr base_op src_data c2 = (src_addr,c3) /\
  emit_op ADD [dst; Lit 32w] c3 = (dst_data,c4) /\
  eval_operand src s = SOME (n2w p) /\
  eval_operand base_op s = SOME (n2w B) /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand cnt s = SOME (n2w n) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st c4) s = OK t /\
    eval_operand sz_op t = SOME (n2w (n*mem_sz)) /\
    eval_operand src_addr t = SOME (n2w (B+p+32)) /\
    eval_operand dst_data t = SOME (n2w (d+32)) /\
    fresh_vars_wrt c4 t /\ inst_extends st c4 /\
    t = s with vs_vars := t.vs_vars /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `eval_operand (Lit (n2w mem_sz)) s = SOME (n2w mem_sz)` by simp[eval_operand_def] >>
  drule_all abi_decode_mul_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >> gvs[word_mul_n2w] >>
  `eval_operand src s1 = SOME (n2w p)` by metis_tac[] >>
  `eval_operand (Lit 32w) s1 = SOME 32w` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand base_op s2 = SOME (n2w B)` by metis_tac[] >>
  `eval_operand src_data s2 = SOME (n2w (p+32))` by simp[word_add_n2w] >>
  drule_all compile_abi_dec_addr_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  `eval_operand dst s3 = SOME (n2w d)` by metis_tac[] >>
  `eval_operand (Lit 32w) s3 = SOME 32w` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c3 c4) s3 = OK s4` >>
  `inst_extends c2 c3` by
    (Cases_on `base_op = Lit 0w` >>
     gvs[compile_abi_dec_addr_def, comp_return_def, inst_extends_refl] >>
     metis_tac[inst_extends_emit_op]) >>
  `run_inst_seq (emitted_insts c2 c4) s2 = OK s4 /\ inst_extends c2 c4` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s3`, `c3`] >> simp[]) >>
  `run_inst_seq (emitted_insts c1 c4) s1 = OK s4 /\ inst_extends c1 c4` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`, `c2`] >> simp[]) >>
  `run_inst_seq (emitted_insts st c4) s = OK s4 /\ inst_extends st c4` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `c1`] >> simp[]) >>
  qexists_tac `s4` >> simp[word_add_n2w] >>
  suspend "exact"
QED

Resume abi_malformed_bulk_pointer_sequence[exact]:
  simp[lookup_var_def] >> irule abi_malformed_read_sequence_frame >>
  goal_assum (drule_at Any) >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`emit_op ADD [dst; Lit 32w] c3 = _`,
     `compile_abi_dec_addr base_op src_data c2 = _`,
     `emit_op ADD [src; Lit 32w] c1 = _`,
     `emit_op MUL _ st = _`] >>
  Cases_on `base_op = Lit 0w` >>
  simp[compile_abi_dec_addr_def, comp_return_def, comp_bind_def, comp_ignore_bind_def, emit_op_def,
    fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, fresh_write_op_def, not_fresh_at_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Finalise abi_malformed_bulk_pointer_sequence

Theorem abi_malformed_bulk_payload_exact:
  abi_decode_bulk_payload dst src cnt mem_sz MLOAD base_op st = ((),en) /\
  eval_operand src s = SOME (n2w p) /\
  eval_operand base_op s = SOME (n2w B) /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand cnt s = SOME (n2w n) /\
  B+p+32 < dimword (:256) /\ d+32 < dimword (:256) /\
  n*mem_sz < dimword (:256) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st en) s = OK t /\ fresh_vars_wrt en t /\
    t = (mcopy (d+32) (B+p+32) (n*mem_sz) s) with vs_vars := t.vs_vars /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
    inst_extends st en
Proof
  simp[abi_decode_bulk_payload_def, comp_bind_def, abi_decode_copy_opcode_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MUL [cnt; Lit (n2w mem_sz)] st = (sz_op,c1)` >>
  rename1 `emit_op ADD [src; Lit 32w] c1 = (src_data,c2)` >>
  rename1 `compile_abi_dec_addr base_op src_data c2 = (src_addr,c3)` >>
  rename1 `emit_op ADD [dst; Lit 32w] c3 = (dst_data,c4)` >>
  drule_all abi_malformed_bulk_pointer_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c4) s = OK s4` >>
  drule_all emit_void_MCOPY_correct >> strip_tac >>
  gvs[w2n_n2w, LESS_MOD] >>
  drule inst_extends_emit_void >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  gvs[] >> qpat_assum `s4 = s with vs_vars := _` SUBST1_TAC >>
  simp_tac std_ss [mcopy_def, write_memory_with_expansion_def, LET_THM,
    venom_state_accfupds, venom_state_fupdfupds, venom_state_component_equality,
    lookup_var_def] >> fs[lookup_var_def]
QED

Theorem abi_malformed_bulk_body_exact:
  abi_decode_bulk_body dst src addr MLOAD base_op mem_sz st = ((),en) /\
  eval_operand src s = SOME (n2w p) /\
  eval_operand base_op s = SOME (n2w B) /\
  eval_operand addr s = SOME a /\ eval_operand dst s = SOME (n2w d) /\
  mload (w2n a) s = n2w n /\
  B+p+32 < dimword (:256) /\ d+32 < dimword (:256) /\
  n*mem_sz < dimword (:256) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st en) s = OK t /\ fresh_vars_wrt en t /\
    t = (mcopy (d+32) (B+p+32) (n*mem_sz) (mstore d (n2w n) s))
          with vs_vars := t.vs_vars /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
    inst_extends st en
Proof
  simp[abi_decode_bulk_body_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_decode_array_header dst addr MLOAD st = (cnt,c1)` >>
  `d < dimword (:256)` by decide_tac >>
  drule_all abi_malformed_array_header_exact >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME (n2w p) /\
   eval_operand base_op s1 = SOME (n2w B) /\
   eval_operand dst s1 = SOME (n2w d)` by metis_tac[] >>
  `eval_operand cnt s1 = SOME (n2w n)` by metis_tac[] >>
  drule abi_malformed_bulk_payload_exact >>
  disch_then (qspecl_then [`s1`, `p`, `n`, `d`, `B`] mp_tac) >>
  (impl_tac >- (rewrite_tac[GSYM ADD_ASSOC] >> simp[])) >> strip_tac >>
  `inst_extends st c1` by
    (fs[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def] >> rpt (pairarg_tac >> gvs[]) >>
     metis_tac[inst_extends_emit_op, inst_extends_emit_void, inst_extends_trans]) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  `st.cs_next_var <= c1.cs_next_var` by
    (fs[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
        fresh_id_def, emit_def] >> rpt (pairarg_tac >> gvs[]) >> gvs[]) >>
  `!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s` by
    metis_tac[not_fresh_at_mono] >>
  qexists_tac `t` >> simp[] >>
  qpat_assum `t = _ with vs_vars := _` SUBST1_TAC >>
  qpat_assum `s1 = _ with vs_vars := _` SUBST1_TAC >>
  qpat_assum `mload (w2n a) s = _` (fn th => rewrite_tac[th]) >>
  simp_tac std_ss [AC MULT_ASSOC MULT_COMM, GSYM ADD_ASSOC] >>
  simp_tac std_ss [mcopy_def, mstore_def, write_memory_with_expansion_def,
    LET_THM, venom_state_accfupds, venom_state_fupdfupds,
    venom_state_component_equality]
QED

Theorem abi_malformed_bulk_body_resource:
  abi_decode_bulk_body dst src addr MLOAD base_op mem_sz st = ((),en) /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  eval_operand addr s = SOME a /\ mload (w2n a) s = n2w n /\
  B+p+32 < dimword (:256) /\ d+32 < dimword (:256) /\
  n*mem_sz < dimword (:256) /\ 32+n*mem_sz <= outsz /\
  fresh_vars_wrt st s /\ fn_inst_ids_distinct func ==>
  ?t. run_inst_seq (emitted_insts st en) s = OK t /\ fresh_vars_wrt en t /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t /\
    inst_extends st en
Proof
  strip_tac >>
  `eval_operand src s = SOME (n2w p) /\
   eval_operand base_op s = SOME (n2w B) /\
   eval_operand dst s = SOME (n2w d)` by fs[abi_malformed_entry_def] >>
  drule_all abi_malformed_bulk_body_exact >> strip_tac >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s
     (mstore d (n2w n) s)` by
    (irule (SRULE [] (Q.INST [`vars` |-> `s.vs_vars`]
       abi_malformed_destination_store_resource)) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz (mstore d (n2w n) s)` by
    (irule abi_malformed_child_entry >>
     `p < dimword (:256) /\ d+outsz < dimword (:256) /\
      eval_operand dst (mstore d (n2w n) s) = SOME (n2w d) /\
      eval_operand src (mstore d (n2w n) s) = SOME (n2w p) /\
      EVERY (abi_decoder_operand_live st.cs_next_var) [base_op;hi;src;dst] /\
      local_ptrs_reserved cenv st` by
       fs[abi_malformed_entry_def, abi_malformed_resource_post_def] >>
     simp[] >> goal_assum (drule_at Any) >> simp[] >> metis_tac[LESS_EQ_REFL]) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid
     (mstore d (n2w n) s)
     (mcopy (d+32) (B+p+32) (n*mem_sz) (mstore d (n2w n) s))` by
    (irule abi_malformed_destination_copy_resource >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule_all abi_malformed_resource_trans >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  irule abi_malformed_resource_register_update >>
  conj_tac >- fs[abi_malformed_entry_def] >>
  qexists_tac `mcopy (d+32) (B+p+32) (n*mem_sz) (mstore d (n2w n) s)` >>
  reverse conj_tac >- simp[] >>
  simp_tac std_ss [lookup_var_def, mcopy_def, mstore_def,
                   write_memory_with_expansion_def, LET_THM,
                   venom_state_accfupds] >>
  qpat_x_assum `!x. not_fresh_at st x ==> _` mp_tac >>
  simp_tac std_ss [lookup_var_def]
QED

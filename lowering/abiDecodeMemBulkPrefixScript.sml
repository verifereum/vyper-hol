(* Bounded, rejection-aware memory execution before bulk-array writes. *)
Theory abiDecodeMemBulkPrefix
Ancestors
  abiDecoderReentry abiDecodeMemBulk abiDecodeMemBytesGuards abiDecodeMemCountGuard
  abiDecoderDynarrayPrefix abiDecoderDynarrayBound abiDecoderBytesBound
  abiDecoderBytesPrefix abiDecoderGuards abiDecoderContract abiDecoderRange abiEncoder
  localPtrsProps fragGasMode fragGasPathMem fragExec
  loweringStateRelDefs emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomState venomInst words arithmetic arithmeticProps list rich_list

Theorem abi_decode_dynarray_payload_fragment[local]:
  abi_decode_dynarray_payload_guard head cnt stride hi st = ((),st') ==>
  inst_extends st st' /\ st'.cs_blocks = st.cs_blocks /\
  st'.cs_current_bb = st.cs_current_bb
Proof
  strip_tac >> drule abi_decode_dynarray_payload_guard_shape >> strip_tac >>
  Cases_on `hi = Lit 0w` >>
  gvs[abi_decode_dynarray_payload_guard_def, compile_abi_decode_range_check_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def]
QED

Theorem abi_decode_dynarray_position_prefix_path_mem:
  abi_decode_dynarray_position_prefix pos MLOAD base_op hi maxn stride st = (addr,st') /\
  base_op <> Lit 0w /\ hi <> Lit 0w /\
  eval_operand pos s = SOME (n2w p) /\ eval_operand base_op s = SOME (n2w b) /\
  eval_operand hi s = SOME (n2w h) /\ p < dimword (:256) /\
  b+h < dimword (:256) /\ b+h <= s.vs_alloca_next /\
  maxn < dimword (:256) /\ maxn*stride < dimword (:256) /\
  fresh_vars_wrt st s /\ fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t)) \/
  (?c t. c <= maxn /\ p+32+c*stride <= h /\
    abi_decode_load MLOAD (n2w (b+p) : bytes32) s = n2w c /\
    gas_path_mem ctx func s 0 (OK t) /\
    eval_operand addr t = SOME (n2w (b+p)) /\
    t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_allocas = s.vs_allocas /\ alloca_history func t)
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_dynarray_position_prefix _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_dynarray_position_prefix_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[comp_return_def] >>
  rename1 `abi_decode_bytes_head pos hi st = (head,c1)` >>
  rename1 `compile_abi_dec_addr base_op pos c1 = (addr,c2)` >>
  rename1 `abi_decode_count_guard MLOAD addr maxn c2 = (cnt,c3)` >>
  rename1 `abi_decode_dynarray_payload_guard head cnt stride hi c3 = ((),st')` >>
  `emit_op ADD [base_op;pos] c1 = (addr,c2)` by gvs[compile_abi_dec_addr_def] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule abi_decode_bytes_head_fragment_shape >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  drule_all abi_decode_count_guard_fragment_shape >> strip_tac >>
  drule abi_decode_dynarray_payload_fragment >> strip_tac >>
  `st.cs_next_var <= c1.cs_next_var` by
    (qpat_x_assum `abi_decode_bytes_head _ _ _ = _` mp_tac >>
     simp[abi_decode_bytes_head_def, compile_abi_decode_range_check_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
       emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[]) >>
  `c1.cs_next_var <= c2.cs_next_var` by
    (drule emitted_insts_emit_op >> simp[]) >>
  `c2.cs_next_var <= c3.cs_next_var` by
    (qpat_x_assum `abi_decode_count_guard _ _ _ _ = _` mp_tac >>
     simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> strip_tac >> gvs[]) >>
  `fn_has_code st c1 func /\ fn_has_code c1 c2 func /\
   fn_has_code c2 c3 func /\ fn_has_code c3 st' func` by
    (gvs[fn_has_code_def, emitted_blocks_def, inst_extends_def, same_blocks_def] >>
     metis_tac[IS_PREFIX_APPEND, APPEND_ASSOC]) >>
  drule_all abi_decode_bytes_head_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  Cases_on `w2n (n2w p : bytes32) <= w2n (n2w p + 32w : bytes32) /\
    w2n (n2w p + 32w : bytes32) <= w2n (n2w h : bytes32)`
  >- suspend "head_accept" >>
  gvs[] >> metis_tac[]
QED
Resume abi_decode_dynarray_position_prefix_path_mem[head_accept]:
  `p+32 < dimword (:256)` by
    (spose_not_then assume_tac >>
     `w2n ((n2w p : bytes32) + 32w) < w2n (n2w p : bytes32)` by
       (irule w2n_add_overflow >> gvs[w2n_n2w, dimword_def]) >>
     gvs[w2n_n2w]) >>
  `h < dimword (:256) /\ p+32 <= h` by gvs[word_add_n2w, w2n_n2w] >>
  gvs[word_add_n2w, w2n_n2w] >>
  rename1 `gas_path_mem ctx func s 0 (OK s1)` >>
  `eval_operand base_op s1 = SOME (n2w b) /\ eval_operand pos s1 = SOME (n2w p)`
    by metis_tac[] >>
  `alloca_inv s1` by (irule alloca_inv_fields >> metis_tac[]) >>
  `s1.vs_current_bb = c1.cs_current_bb` by simp[] >>
  drule_all abi_decode_add_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path_mem ctx func s1 0 (OK s2)` >>
  `gas_path_mem ctx func s 0 (OK s2)` by metis_tac[gas_path_mem_then, ADD_CLAUSES] >>
  `b+p < dimword (:256) /\ b+p+32 <= s2.vs_alloca_next` by decide_tac >>
  `eval_operand addr s2 = SOME (n2w (b+p))` by gvs[word_add_n2w] >>
  `alloca_inv s2` by (irule alloca_inv_fields >> metis_tac[]) >>
  `w2n (n2w (b+p) : bytes32)+32 <= s2.vs_alloca_next` by simp[w2n_n2w] >>
  drule_all abi_decode_mload_count_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  Cases_on `w2n (abi_decode_load MLOAD (n2w (b+p) : bytes32) s2) <= maxn`
  >- suspend "count_accept" >>
  `maxn < w2n (abi_decode_load MLOAD (n2w (b+p) : bytes32) s2)` by decide_tac >>
  gvs[GSYM word_add_n2w] >> disj1_tac >> fs[gas_marked_path_def] >>
  drule_all gas_path_mem_then >> simp[] >> metis_tac[]
QED
Resume abi_decode_dynarray_position_prefix_path_mem[count_accept]:
  gvs[GSYM word_add_n2w] >>
  rename1 `gas_path_mem ctx func s2 0 (OK s3)` >>
  `gas_path_mem ctx func s 0 (OK s3)` by metis_tac[gas_path_mem_then, ADD_CLAUSES] >>
  `abi_decode_load MLOAD (n2w (b+p) : bytes32) s2 =
   abi_decode_load MLOAD (n2w (b+p) : bytes32) s` by simp[abi_decode_load_def, mload_def] >>
  qmatch_asmsub_abbrev_tac `w2n cw <= maxn` >>
  `w2n cw*stride <= maxn*stride` by simp[LE_MULT_RCANCEL] >>
  `w2n cw*stride < dimword (:256)` by decide_tac >>
  `eval_operand head s3 = SOME (n2w (p+32)) /\ eval_operand hi s3 = SOME (n2w h)` by
    (simp[word_add_n2w] >> metis_tac[]) >>
  `alloca_inv s3` by (irule alloca_inv_fields >> metis_tac[]) >>
  `s3.vs_current_bb = c3.cs_current_bb` by simp[] >>
  drule_all abi_decode_dynarray_payload_guard_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  Cases_on `w2n (n2w (p+32) : bytes32) <=
      w2n ((n2w (p+32) : bytes32) + cw*n2w stride) /\
    w2n ((n2w (p+32) : bytes32) + cw*n2w stride) <= w2n (n2w h : bytes32)`
  >- suspend "payload_accept" >>
  gvs[] >> disj1_tac >> fs[gas_marked_path_def] >>
  drule_all gas_path_mem_then >> simp[] >> metis_tac[]
QED
Resume abi_decode_dynarray_position_prefix_path_mem[payload_accept]:
  `h < dimword (:256) /\ p+32 < dimword (:256)` by decide_tac >>
  `cw*n2w stride = (n2w (w2n cw*stride) : bytes32)` by simp[word_mul_def] >>
  `p+32+w2n cw*stride < dimword (:256)` by
    (spose_not_then assume_tac >>
     mp_tac (Q.SPECL [`n2w (p+32)`, `cw*n2w stride`] w2n_add_overflow) >>
     gvs[w2n_n2w]) >>
  `p+32+w2n cw*stride <= h` by fs[w2n_add_2, w2n_n2w] >>
  fs[w2n_add_2, w2n_n2w] >>
  rename1 `gas_path_mem ctx func s3 0 (OK t)` >>
  `gas_path_mem ctx func s 0 (OK t)` by metis_tac[gas_path_mem_then, ADD_CLAUSES] >>
  `abi_decode_load MLOAD (n2w (b+p) : bytes32) s = cw` by
    gvs[Abbr `cw`, word_add_n2w] >>
  `eval_operand addr t = SOME (n2w (b+p))` by
    (qpat_x_assum `!op w. eval_operand op s3 = _ ==> _` irule >>
     qpat_x_assum `!op w. eval_operand op s2 = _ ==> _` irule >>
     simp[word_add_n2w]) >>
  `!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w` by
    (rpt strip_tac >>
     qpat_x_assum `!op w. eval_operand op s3 = _ ==> _` irule >>
     qpat_x_assum `!op w. eval_operand op s2 = _ ==> _` irule >>
     qpat_x_assum `!op w. eval_operand op s1 = _ ==> _` irule >>
     metis_tac[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (rpt strip_tac >>
     `abi_decoder_operand_live c1.cs_next_var op /\
      abi_decoder_operand_live c2.cs_next_var op /\
      abi_decoder_operand_live c3.cs_next_var op` by
       metis_tac[abi_decoder_operand_live_mono] >>
     metis_tac[]) >>
  disj2_tac >> qexistsl_tac [`w2n cw`, `t`] >> simp[word_add_n2w]
QED
Finalise abi_decode_dynarray_position_prefix_path_mem

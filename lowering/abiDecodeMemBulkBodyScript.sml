(* Bounded memory execution of bulk dynamic-array writes. *)
Theory abiDecodeMemBulkBody
Ancestors
  abiDecoderBulk abiDecoderArrayHeader abiDecoderComposition abiDecoderContract
  abiDecoderGuards abiDecoderRange abiDecoderDynarrayBound abiDecoderBytesBound
  abiEncoder abiDecoderReservation abiDecoderArrayLoopInit allocaFootprint fragExecMem
  fragGasPathMem fragGasSeqMem entryDecoderHistoryFrame allocaHistoryFragment
  entrySinkExtraction loweringStateRelDefs
  fragExec emitHelperProps exprLoweringProps compileEnv emitHelper
  instMemFrontier memSafeRun contextCodegenRel venomExecSemantics venomState venomInst words arithmetic list rich_list

Theorem abi_decode_array_header_mem_ok:
  abi_decode_array_header dst addr MLOAD st = (cnt,st') /\
  eval_operand addr s = SOME a /\ eval_operand dst s = SOME (n2w d) /\
  d < dimword (:256) /\ w2n a+32 <= s.vs_alloca_next /\
  d+32 <= s.vs_alloca_next /\ fresh_vars_wrt st s ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  simp_tac bool_ss [abi_decode_array_header_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MLOAD [addr] st = (cnt,c1)` >>
  rename1 `emit_void MSTORE [dst;cnt] c1 = ((),st')` >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand dst s1 = SOME (n2w d)` by metis_tac[] >>
  `s1.vs_alloca_next = s.vs_alloca_next` by
    (drule emitted_insts_emit_op >> strip_tac >>
     qpat_x_assum `run_inst_seq _ s = OK s1` mp_tac >>
     simp[run_inst_seq_def, Once step_inst_base_def, exec_read1_def,
       mk_inst_def, update_var_def, eval_operand_def, abi_decode_load_def] >>
     strip_tac >> gvs[]) >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `run_inst_seq_mem_ok (emitted_insts st c1) s` by
    (metis_tac[emit_mload_mem_ok]) >>
  qpat_x_assum `emitted_insts st st' = _` SUBST1_TAC >>
  irule run_inst_seq_mem_ok_append >> simp[] >>
  irule emit_mstore_mem_ok >>
  qexistsl_tac [`n2w d`, `dst`, `cnt`] >> simp[w2n_n2w]
QED

Theorem abi_decode_bulk_copy_prepare[local]:
  emit_op MUL [cnt; Lit (n2w msz)] st = (sz,c1) /\
  emit_op ADD [src; Lit 32w] c1 = (src_data,c2) /\
  compile_abi_dec_addr base_op src_data c2 = (src_addr,c3) /\
  emit_op ADD [dst; Lit 32w] c3 = (dst_data,c4) /\ base_op <> Lit 0w /\
  eval_operand src s = SOME (n2w p) /\ eval_operand base_op s = SOME (n2w b) /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand cnt s = SOME (n2w c) /\
  fresh_vars_wrt st s ==>
  ?s4. run_inst_seq (emitted_insts st c4) s = OK s4 /\
    run_inst_seq_mem_ok (emitted_insts st c4) s /\ inst_extends st c4 /\
    s4.vs_alloca_next = s.vs_alloca_next /\
    eval_operand sz s4 = SOME (n2w (c*msz)) /\
    eval_operand src_addr s4 = SOME (n2w (b+p+32)) /\
    eval_operand dst_data s4 = SOME (n2w (d+32))
Proof
  strip_tac >>
  `eval_operand (Lit (n2w msz)) s = SOME (n2w msz)` by simp[eval_operand_def] >>
  drule_all abi_decode_mul_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME (n2w p) /\ eval_operand (Lit 32w) s1 = SOME 32w`
    by (simp[eval_operand_def] >> metis_tac[]) >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand base_op s2 = SOME (n2w b) /\
   eval_operand src_data s2 = SOME (n2w (p+32))` by (simp[word_add_n2w] >> metis_tac[]) >>
  drule_all compile_abi_dec_addr_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  `eval_operand dst s3 = SOME (n2w d) /\ eval_operand (Lit 32w) s3 = SOME 32w`
    by (simp[eval_operand_def] >> metis_tac[]) >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c3 c4) s3 = OK s4` >>
  `eval_operand sz s4 = SOME (n2w (c*msz)) /\
   eval_operand src_addr s4 = SOME (n2w (b+p+32))` by
    (pure_rewrite_tac[GSYM ADD_ASSOC] >> metis_tac[word_mul_n2w, ADD_ASSOC]) >>
  `inst_extends c2 c3` by
    (gvs[compile_abi_dec_addr_def] >> metis_tac[inst_extends_emit_op]) >>
  `inst_extends st c2 /\ inst_extends st c3 /\ inst_extends st c4` by
    metis_tac[inst_extends_trans] >>
  `emitted_insts st c4 = emitted_insts st c1 ++
    (emitted_insts c1 c2 ++ (emitted_insts c2 c3 ++ emitted_insts c3 c4))` by
    (`emitted_insts st c2 = emitted_insts st c1 ++ emitted_insts c1 c2` by
       (irule emitted_insts_append >> fs[inst_extends_def]) >>
     `emitted_insts st c3 = emitted_insts st c2 ++ emitted_insts c2 c3` by
       (irule emitted_insts_append >> fs[inst_extends_def]) >>
     `emitted_insts st c4 = emitted_insts st c3 ++ emitted_insts c3 c4` by
       (irule emitted_insts_append >> fs[inst_extends_def]) >> simp[APPEND_ASSOC]) >>
  `run_inst_seq (emitted_insts st c4) s = OK s4` by
    (qpat_assum `run_inst_seq _ s = OK s1` (mp_tac o MATCH_MP run_inst_seq_append) >>
     qpat_assum `run_inst_seq _ s1 = OK s2` (mp_tac o MATCH_MP run_inst_seq_append) >>
     qpat_assum `run_inst_seq _ s2 = OK s3` (mp_tac o MATCH_MP run_inst_seq_append) >>
     simp_tac bool_ss [] >> metis_tac[]) >>
  qexists_tac `s4` >> simp[GSYM word_add_n2w] >>
  gvs[compile_abi_dec_addr_def] >>
  rpt (qpat_x_assum `emit_op _ _ _ = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_op)) >>
  conj_tac >- (irule run_inst_seq_mem_ok_every >>
    simp[below_frontier_no_ranges, inst_dload_in_section_def, mk_inst_def, is_alloca_op_def]) >>
  gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
    exec_pure2_def, update_var_def, eval_operand_def, AllCaseEqs()]
QED

Theorem abi_decode_bulk_payload_mem_ok[local]:
  abi_decode_bulk_payload dst src cnt msz MLOAD base_op st = ((),st') /\
  base_op <> Lit 0w /\
  eval_operand src s = SOME (n2w p) /\ eval_operand base_op s = SOME (n2w b) /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand cnt s = SOME (n2w c) /\
  b+p+32 < dimword (:256) /\ d+32 < dimword (:256) /\ c*msz < dimword (:256) /\
  b+p+32+c*msz <= s.vs_alloca_next /\ d+32+c*msz <= s.vs_alloca_next /\
  fresh_vars_wrt st s ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  simp_tac bool_ss [abi_decode_bulk_payload_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_void (abi_decode_copy_opcode MLOAD) _ c4 = ((),st')` >>
  drule_all abi_decode_bulk_copy_prepare >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c4) s = OK s4` >>
  `inst_extends c4 st'` by metis_tac[inst_extends_emit_void] >>
  `emitted_insts st st' = emitted_insts st c4 ++ emitted_insts c4 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def] >> gvs[APPEND_ASSOC]) >>
  qpat_x_assum `emitted_insts st st' = _` SUBST1_TAC >>
  irule run_inst_seq_mem_ok_append >> simp[] >>
  gvs[abi_decode_copy_opcode_def] >> irule emit_mcopy_mem_ok >>
  qexistsl_tac [`n2w (b+p+32)`, `n2w (d+32)`, `dst_data`,
    `copy_sz`, `n2w (c*msz)`, `src_addr`] >>
  simp[w2n_n2w] >> decide_tac
QED

Theorem abi_decode_bulk_body_mem_ok:
  abi_decode_bulk_body dst pos addr MLOAD base_op msz st = ((),st') /\
  base_op <> Lit 0w /\
  eval_operand pos s = SOME (n2w p) /\ eval_operand base_op s = SOME (n2w b) /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand addr s = SOME (n2w (b+p)) /\
  abi_decode_load MLOAD (n2w (b+p) : bytes32) s = n2w c /\
  b+p+32 < dimword (:256) /\ d+32 < dimword (:256) /\
  c*msz < dimword (:256) /\ b+p+32+c*msz <= s.vs_alloca_next /\
  d+32+c*msz <= s.vs_alloca_next /\ fresh_vars_wrt st s ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  simp_tac bool_ss [abi_decode_bulk_body_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_decode_array_header dst addr MLOAD st = (cnt,c1)` >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `d < dimword (:256)` by decide_tac >>
  drule_all abi_decode_array_header_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  `s1.vs_alloca_next = s.vs_alloca_next` by
    (`EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
        (emitted_insts st c1)` by fs[EVERY_MEM] >>
     drule_all abi_decode_sequence_allocation_frame >> simp[]) >>
  `eval_operand pos s1 = SOME (n2w p) /\
   eval_operand base_op s1 = SOME (n2w b) /\
   eval_operand dst s1 = SOME (n2w d)` by metis_tac[] >>
  `run_inst_seq_mem_ok (emitted_insts st c1) s` by
    (irule abi_decode_array_header_mem_ok >> reverse conj_tac >- simp[] >>
     qexistsl_tac [`n2w (b+p)`, `addr`, `cnt`, `d`, `dst`] >>
     simp[w2n_n2w] >> decide_tac) >>
  `eval_operand cnt s1 = SOME (n2w c)` by
    (qpat_x_assum `eval_operand _ _ = SOME (abi_decode_load _ _ _)` mp_tac >>
     asm_rewrite_tac[]) >>
  `b+p+32 < dimword (:256)` by decide_tac >>
  `inst_extends c1 st'` by
    (drule_all abi_decode_bulk_payload_sequence >> strip_tac >> simp[]) >>
  `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  qpat_x_assum `emitted_insts st st' = _` SUBST1_TAC >>
  irule run_inst_seq_mem_ok_append >> simp[] >>
  irule abi_decode_bulk_payload_mem_ok >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`b`, `base_op`, `c`, `cnt`, `d`, `dst`, `msz`, `p`, `pos`] >> simp[]
QED

Theorem abi_decode_bulk_body_memory_shape[local]:
  abi_decode_bulk_body dst pos addr MLOAD base_op msz st = ((),st') ==>
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st') /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st') = []
Proof
  Cases_on `base_op = Lit 0w` >>
  simp[abi_decode_bulk_body_def, abi_decode_array_header_def,
    abi_decode_bulk_payload_def, compile_abi_dec_addr_def, abi_decode_copy_opcode_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def, LET_THM] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def]
QED

Theorem abi_decode_bulk_body_path_mem:
  abi_decode_bulk_body dst pos addr MLOAD base_op msz st = ((),st') /\
  base_op <> Lit 0w /\
  eval_operand pos s = SOME (n2w p) /\ eval_operand base_op s = SOME (n2w b) /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand addr s = SOME (n2w (b+p)) /\
  abi_decode_load MLOAD (n2w (b+p) : bytes32) s = n2w c /\
  b+p+32 < dimword (:256) /\ d+32 < dimword (:256) /\
  c*msz < dimword (:256) /\ b+p+32+c*msz <= s.vs_alloca_next /\
  d+32+c*msz <= s.vs_alloca_next /\
  (b+p+32+c*msz <= d \/ d+32+c*msz <= b+p) /\
  fresh_vars_wrt st s /\ fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    mem_word_at d t.vs_memory = n2w c /\
    mem_bytes_at (d+32) (c*msz) t.vs_memory =
      mem_bytes_at (b+p+32) (c*msz) s.vs_memory /\
    abi_decode_frame d (32+c*msz) s t /\
    mem_bytes_at (b+p) (32+c*msz) t.vs_memory =
      mem_bytes_at (b+p) (32+c*msz) s.vs_memory /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
    alloca_history func t
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  mp_tac (Q.INST [`opc` |-> `MLOAD`, `src` |-> `pos`, `sb` |-> `p`,
    `src_base` |-> `b`, `n` |-> `c`, `mem_sz` |-> `msz`]
    abi_decode_bulk_body_sequence) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >>
  drule_all abi_decode_bulk_body_mem_ok >> strip_tac >>
  drule_all abi_decode_bulk_body_shape >> strip_tac >>
  drule abi_decode_bulk_body_memory_shape >> strip_tac >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by fs[inst_extends_def] >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)`
    by simp[IS_PREFIX_APPEND] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st st')`
    by fs[EVERY_MEM] >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule_all entry_straight_line_alloca_history >> strip_tac >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts st st') = LENGTH st'.cs_current_insts`
    by (gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `mem_bytes_at (b+p) (32+c*msz) t.vs_memory =
     mem_bytes_at (b+p) (32+c*msz) s.vs_memory` by
    (qpat_assum `abi_decode_frame _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_decode_frame_def] >> strip_tac >>
     first_x_assum irule >> decide_tac) >>
  qexists_tac `t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def, abi_decode_source_def, abi_decode_frame_def] >>
  gvs[fresh_vars_wrt_def, abi_decode_frame_def] >> first_assum ACCEPT_TAC
QED

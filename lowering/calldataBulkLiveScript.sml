(* Bulk decoder execution over reentrant register states. *)
Theory calldataBulkLive
Ancestors
  valueEncodingDefs safeSequence calldataWordLeaf calldataBytesLeaf calldataBytesLive calldataBulkLeaf calldataDynOwned abiDecoderReentry
  abiDecoderFrameCompose abiDecoderBulk abiDecoderCopy abiDecoderComposition abiDecoderContract abiDecoderGuards abiDecoderRange abiEncoder
  emitHelperProps exprLoweringProps compileEnv emitHelper valueEncoding
  venomExecSemantics venomState venomInst words arithmetic list

Theorem calldata_bulk_payload_live:
  abi_decode_bulk_payload dst src cnt mem_sz CALLDATALOAD (Lit 0w) st = ((),st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  eval_operand cnt s = SOME (n2w n) /\ d + 32 < dimword (:256) /\
  n * mem_sz < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var cnt ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_bytes_at (d+32) (n*mem_sz) t.vs_memory =
      mem_bytes_at (w2n (p+32w)) (n*mem_sz) s.vs_call_ctx.cc_calldata /\
    abi_decode_frame (d+32) (n*mem_sz) s t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    inst_extends st st'
Proof
  simp[abi_decode_bulk_payload_def, compile_abi_dec_addr_def, comp_return_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MUL [cnt; Lit (n2w mem_sz)] st = (sz_op,c1)` >>
  rename1 `emit_op ADD [src; Lit 32w] c1 = (src_data,c2)` >>
  rename1 `emit_op ADD [dst; Lit 32w] c2 = (dst_data,c3)` >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac abi_decoder_operand_live_emit >>
  `eval_operand (Lit (n2w mem_sz)) s = SOME (n2w mem_sz)` by simp[eval_operand_def] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `MUL`] calldata_binary_repeat)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME p` by metis_tac[] >>
  `eval_operand (Lit 32w) s1 = SOME 32w` by simp[eval_operand_def] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] calldata_binary_repeat)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `abi_decoder_operand_live c1.cs_next_var dst` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand dst s2 = SOME (n2w d)` by metis_tac[] >>
  `eval_operand (Lit 32w) s2 = SOME 32w` by simp[eval_operand_def] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] calldata_binary_repeat)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  `abi_decoder_operand_live c2.cs_next_var sz_op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `c1.cs_next_var` >> simp[]) >>
  `eval_operand sz_op s3 = SOME (n2w (n*mem_sz)) /\
   eval_operand src_data s3 = SOME (p+32w)` by
    (gvs[word_mul_n2w] >> metis_tac[]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `eval_operand dst_data s3 = SOME (n2w (d+32))` by simp[word_add_n2w] >>
  drule_all abi_decode_copy_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c3 st') s3 = OK t` >>
  drule_all abi_decode_copy_vars >> strip_tac >>
  drule inst_extends_emit_void >> strip_tac >>
  `run_inst_seq (emitted_insts c2 st') s2 = OK t /\ inst_extends c2 st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s3`,`c3`] >> simp[]) >>
  `run_inst_seq (emitted_insts c1 st') s1 = OK t /\ inst_extends c1 st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`,`c2`] >> simp[]) >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`,`c1`] >> simp[]) >>
  `step_inst_base (mk_inst c3.cs_next_id (abi_decode_copy_opcode CALLDATALOAD)
     [dst_data;src_data;sz_op] []) s3 =
     OK (write_memory_with_expansion (d+32)
       (abi_decode_copy_bytes CALLDATALOAD (w2n (p+32w)) (n*mem_sz) s3) s3)` by
    (`d+32 = w2n (n2w (d+32):bytes32) /\
      n*mem_sz = w2n (n2w (n*mem_sz):bytes32)` by simp[w2n_n2w] >>
     once_asm_rewrite_tac[] >> irule abi_decode_copy_step >> gvs[]) >>
  drule emitted_insts_emit_void >> strip_tac >>
  `t.vs_allocas = s3.vs_allocas /\ t.vs_alloca_next = s3.vs_alloca_next /\
   t.vs_labels = s3.vs_labels` by
    (gvs[run_inst_seq_def, write_memory_with_expansion_def]) >>
  qexists_tac `t` >>
  gvs[w2n_n2w, word_mul_n2w, abi_decode_copy_bytes_def,
      abi_decode_source_def, mem_bytes_at_def, abi_decode_frame_def] >>
  conj_tac >- metis_tac[] >> rpt strip_tac >>
  `abi_decoder_operand_live (st.cs_next_var+1) op /\
   abi_decoder_operand_live (st.cs_next_var+2) op` by
    (conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand op s3 = eval_operand op s` by metis_tac[] >>
  Cases_on `op` >> gvs[eval_operand_def, lookup_var_def]
QED

Theorem calldata_bulk_body_live:
  abi_decode_bulk_body dst src src CALLDATALOAD (Lit 0w) mem_sz st = ((),st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  abi_decode_load CALLDATALOAD p s = n2w n /\
  d+32 < dimword (:256) /\ n*mem_sz < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_word_at d t.vs_memory = n2w n /\
    mem_bytes_at (d+32) (n*mem_sz) t.vs_memory =
      mem_bytes_at (w2n (p+32w)) (n*mem_sz) s.vs_call_ctx.cc_calldata /\
    abi_decode_frame d (32+n*mem_sz) s t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    inst_extends st st'
Proof
  simp_tac bool_ss [abi_decode_bulk_body_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_decode_array_header dst src CALLDATALOAD st = (cnt,c1)` >>
  `d < dimword (:256)` by decide_tac >>
  drule_all calldata_array_header_repeat_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME p /\ eval_operand dst s1 = SOME (n2w d)` by metis_tac[] >>
  `st.cs_next_var <= c1.cs_next_var /\
   abi_decoder_operand_live c1.cs_next_var cnt` by
    (qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
     simp[abiDecoderArrayHeaderTheory.abi_decode_array_header_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
     imp_res_tac emitted_insts_emit_op >>
     drule emitted_insts_emit_void >> strip_tac >>
     gvs[] >> metis_tac[abi_decoder_operand_live_emit]) >>
  `abi_decoder_operand_live c1.cs_next_var src /\
   abi_decoder_operand_live c1.cs_next_var dst` by
    (conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand cnt s1 = SOME (n2w n)` by simp[] >>
  drule calldata_bulk_payload_live >>
  disch_then (qspecl_then [`s1`,`p`,`n`,`d`] mp_tac) >>
  simp[MULT_COMM] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`,`c1`] >> simp[]) >>
  `mem_word_at d t.vs_memory = mem_word_at d s1.vs_memory` by
    (irule abi_decode_frame_mem_word >>
     qexistsl_tac [`d+32`,`mem_sz*n`] >> simp[]) >>
  `s1.vs_call_ctx = s.vs_call_ctx` by gvs[abi_decode_frame_def] >>
  `abi_decode_frame d (32+mem_sz*n) s t` by
    (irule abi_decode_frame_adjacent >> qexists_tac `s1` >> simp[]) >>
  qexists_tac `t` >> gvs[] >> rpt strip_tac >>
  `abi_decoder_operand_live c1.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> simp[]) >> metis_tac[]
QED

Theorem calldata_bulk_accepted_live:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  d+32 < dimword (:256) /\
  w2n (abi_decode_load CALLDATALOAD p s) * mem_sz < dimword (:256) /\
  maxn < dimword (:256) /\ w2n (abi_decode_load CALLDATALOAD p s) <= maxn ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p s /\
    mem_bytes_at (d+32) (w2n (abi_decode_load CALLDATALOAD p s)*mem_sz) t.vs_memory =
      mem_bytes_at (w2n (p+32w)) (w2n (abi_decode_load CALLDATALOAD p s)*mem_sz)
        s.vs_call_ctx.cc_calldata /\
    abi_decode_frame d (32+w2n (abi_decode_load CALLDATALOAD p s)*mem_sz) s t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bulk_phases,
    abiDecoderDynarrayPrefixTheory.abi_decode_dynarray_prefix_def,
    abiDecoderDynarrayBoundTheory.abi_decode_dynarray_end_guard_def,
    abiDecoderDynarrayPrefixTheory.abi_decode_dynarray_position_prefix_unbounded,
    abiEncoderTheory.compile_abi_dec_addr_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `abi_decode_count_guard CALLDATALOAD src maxn st = (count_op,c1)` >>
  drule_all calldata_count_guard_repeat_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME p /\ eval_operand dst s1 = SOME (n2w d)` by metis_tac[] >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  `st.cs_next_var <= c1.cs_next_var` by
    (qpat_x_assum `abi_decode_count_guard _ _ _ _ = _` mp_tac >>
     simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     imp_res_tac emitted_insts_emit_op >>
     drule emitted_insts_emit_void >> strip_tac >> gvs[]) >>
  `abi_decoder_operand_live c1.cs_next_var src /\
   abi_decoder_operand_live c1.cs_next_var dst` by
    (conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  `abi_decode_load CALLDATALOAD p s1 = abi_decode_load CALLDATALOAD p s` by
    simp[abi_decode_load_def, abi_decode_source_def] >>
  drule calldata_bulk_body_live >>
  disch_then (qspecl_then [`s1`,`p`,`w2n (abi_decode_load CALLDATALOAD p s)`,`d`] mp_tac) >>
  simp[MULT_COMM] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`,`c1`] >> simp[]) >>
  qexists_tac `t` >> gvs[abi_decode_frame_def] >>
  conj_tac >- metis_tac[] >> rpt strip_tac >>
  `abi_decoder_operand_live c1.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  metis_tac[]
QED

Theorem calldata_bulk_rejected_live:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\ eval_operand src s = SOME p /\
  maxn < dimword (:256) /\ maxn < w2n (abi_decode_load CALLDATALOAD p s) ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bulk_phases,
    abiDecoderDynarrayPrefixTheory.abi_decode_dynarray_prefix_def,
    abiDecoderDynarrayBoundTheory.abi_decode_dynarray_end_guard_def,
    abiDecoderDynarrayPrefixTheory.abi_decode_dynarray_position_prefix_unbounded,
    abiEncoderTheory.compile_abi_dec_addr_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `abi_decode_bulk_body dst src src CALLDATALOAD (Lit 0w) mem_sz c1 = ((),st')` >>
  drule_all calldata_count_guard_rejected_live >> strip_tac >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  drule calldata_bulk_body_extends >> strip_tac >>
  qexists_tac `t` >> simp[] >> irule run_inst_seq_abort_extends >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem calldata_bulk_payload_live_prefix_safe:
  abi_decode_bulk_payload dst src cnt mem_sz CALLDATALOAD (Lit 0w) st = ((),st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  eval_operand cnt s = SOME (n2w n) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var cnt /\
  d+32 < dimword (:256) /\ n*mem_sz < dimword (:256) /\
  d+32+n*mem_sz <= s.vs_alloca_next ==>
  !pre i post u. emitted_insts st st' = pre ++ i::post /\
    run_inst_seq pre s = OK u ==> inst_mem_below_frontier i u
Proof
  simp[abi_decode_bulk_payload_def, compile_abi_dec_addr_def, comp_return_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MUL [cnt; Lit (n2w mem_sz)] st = (sz_op,c1)` >>
  rename1 `emit_op ADD [src; Lit 32w] c1 = (src_data,c2)` >>
  rename1 `emit_op ADD [dst; Lit 32w] c2 = (dst_data,c3)` >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac abi_decoder_operand_live_emit >>
  `eval_operand (Lit (n2w mem_sz)) s = SOME (n2w mem_sz)` by simp[eval_operand_def] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `MUL`] calldata_binary_repeat)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME p` by metis_tac[] >>
  `eval_operand (Lit 32w) s1 = SOME 32w` by simp[eval_operand_def] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] calldata_binary_repeat)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `abi_decoder_operand_live c1.cs_next_var dst` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand dst s2 = SOME (n2w d)` by metis_tac[] >>
  `eval_operand (Lit 32w) s2 = SOME 32w` by simp[eval_operand_def] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] calldata_binary_repeat)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  `run_inst_seq (emitted_insts c1 c3) s1 = OK s3 /\ inst_extends c1 c3` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`,`c2`] >> simp[]) >>
  `run_inst_seq (emitted_insts st c3) s = OK s3 /\ inst_extends st c3` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`,`c1`] >> simp[]) >>
  `emitted_insts st c3 = emitted_insts st c1 ++ emitted_insts c1 c2 ++ emitted_insts c2 c3` by
    (irule EQ_TRANS >> qexists_tac `emitted_insts st c1 ++ emitted_insts c1 c3` >>
     conj_tac >- (irule emitted_insts_append >> fs[inst_extends_def]) >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     AP_TERM_TAC >> irule emitted_insts_append >> fs[inst_extends_def]) >>
  `EVERY (\i. !u. inst_mem_below_frontier i u) (emitted_insts st c3)` by
    (asm_rewrite_tac[] >> simp[] >>
     simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def, mk_inst_def]) >>
  drule inst_extends_emit_void >> strip_tac >>
  `emitted_insts st st' = emitted_insts st c3 ++ emitted_insts c3 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  qpat_x_assum `emitted_insts st st' = _` (fn th => once_rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac (GEN_ALL run_inst_seq_prefix_safe_append) >>
  qexists_tac `s3` >> conj_tac
  >- (ho_match_mp_tac calldata_prefix_safe_every >> first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  drule emitted_insts_emit_void >> simp[abi_decode_copy_opcode_def] >> strip_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac (GEN_ALL calldata_variable_copy_prefix_safe) >>
  qexistsl_tac [`n*mem_sz`,`d+32`] >> simp[] >>
  `abi_decoder_operand_live c2.cs_next_var sz_op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `c1.cs_next_var` >> simp[]) >>
  gvs[word_mul_n2w,word_add_n2w] >> metis_tac[]
QED

Theorem calldata_bulk_body_live_prefix_safe:
  abi_decode_bulk_body dst src src CALLDATALOAD (Lit 0w) mem_sz st = ((),st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  d+32 < dimword (:256) /\
  w2n (abi_decode_load CALLDATALOAD p s)*mem_sz < dimword (:256) /\
  d+32+w2n (abi_decode_load CALLDATALOAD p s)*mem_sz <= s.vs_alloca_next ==>
  !pre i post u. emitted_insts st st' = pre ++ i::post /\
    run_inst_seq pre s = OK u ==> inst_mem_below_frontier i u
Proof
  simp_tac bool_ss [abi_decode_bulk_body_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_decode_array_header dst src CALLDATALOAD st = (cnt,c1)` >>
  `d < dimword (:256)` by decide_tac >>
  drule_all calldata_array_header_repeat_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME p /\ eval_operand dst s1 = SOME (n2w d)` by metis_tac[] >>
  `st.cs_next_var <= c1.cs_next_var /\
   abi_decoder_operand_live c1.cs_next_var cnt` by
    (qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
     simp[abiDecoderArrayHeaderTheory.abi_decode_array_header_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
     imp_res_tac emitted_insts_emit_op >>
     drule emitted_insts_emit_void >> strip_tac >>
     gvs[] >> metis_tac[abi_decoder_operand_live_emit]) >>
  `abi_decoder_operand_live c1.cs_next_var src /\
   abi_decoder_operand_live c1.cs_next_var dst` by
    (conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  `inst_extends c1 st'` by
    (qpat_x_assum `abi_decode_bulk_payload _ _ _ _ _ _ _ = _` mp_tac >>
     simp[abi_decode_bulk_payload_def, compile_abi_dec_addr_def, comp_return_def, comp_bind_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
     metis_tac[inst_extends_trans]) >>
  `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  qpat_x_assum `emitted_insts st st' = _` (fn th => once_rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac (GEN_ALL run_inst_seq_prefix_safe_append) >>
  qexists_tac `s1` >> conj_tac
  >- (ho_match_mp_tac (GEN_ALL calldata_array_header_repeat_prefix_safe) >>
      qexistsl_tac [`src`,`p`,`dst`,`d`,`cnt`] >> simp[] >> decide_tac) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  ho_match_mp_tac (GEN_ALL calldata_bulk_payload_live_prefix_safe) >>
  qexistsl_tac [`src`,`p`,`w2n (abi_decode_load CALLDATALOAD p s)`,`mem_sz`,`dst`,`d`,`cnt`] >>
  simp[MULT_COMM]
QED

Theorem calldata_bulk_live_prefix_safe:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\ eval_operand src s = SOME p /\
  eval_operand dst s = SOME (n2w d) /\ maxn < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  d+(32+maxn*mem_sz) < dimword (:256) /\
  d+(32+maxn*mem_sz) <= s.vs_alloca_next ==>
  !pre i post u. emitted_insts st st' = pre ++ i::post /\
    run_inst_seq pre s = OK u ==> inst_mem_below_frontier i u
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [calldata_bulk_sentinel, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_decode_count_guard CALLDATALOAD src maxn st = (count_op,c1)` >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  drule calldata_bulk_body_extends >> strip_tac >>
  `st.cs_next_var <= c1.cs_next_var` by
    (qpat_x_assum `abi_decode_count_guard _ _ _ _ = _` mp_tac >>
     simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     imp_res_tac emitted_insts_emit_op >>
     drule emitted_insts_emit_void >> strip_tac >> gvs[]) >>
  `abi_decoder_operand_live c1.cs_next_var src /\
   abi_decoder_operand_live c1.cs_next_var dst` by
    (conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  qpat_x_assum `emitted_insts st st' = _` (fn th => once_rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac calldata_prefix_safe_append >> conj_tac
  >- (ho_match_mp_tac calldata_prefix_safe_every >>
      drule calldata_count_guard_instruction_safe >> simp[]) >>
  gen_tac >> strip_tac >>
  Cases_on `w2n (abi_decode_load CALLDATALOAD p s) <= maxn`
  >- (drule_all calldata_count_guard_repeat_sequence >> strip_tac >> gvs[] >>
      `w2n (abi_decode_load CALLDATALOAD p s)*mem_sz <= maxn*mem_sz` by
        simp[LE_MULT_RCANCEL] >>
      pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      ho_match_mp_tac (GEN_ALL calldata_bulk_body_live_prefix_safe) >>
      `eval_operand src t = SOME p /\ eval_operand dst t = SOME (n2w d)` by metis_tac[] >>
      `abi_decode_load CALLDATALOAD p t = abi_decode_load CALLDATALOAD p s` by
        simp[abi_decode_load_def, abi_decode_source_def] >>
      qexistsl_tac [`src`,`p`,`mem_sz`,`dst`,`d`] >> simp[] >> decide_tac) >>
  `maxn < w2n (abi_decode_load CALLDATALOAD p s)` by decide_tac >>
  drule_all calldata_count_guard_rejected_live >> gvs[]
QED

Theorem calldata_bulk_live_frag_mem:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\ eval_operand src initial = SOME p /\
  eval_operand dst initial = SOME (n2w d) /\ maxn < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  d+(32+maxn*mem_sz) < dimword (:256) /\
  d+(32+maxn*mem_sz) <= initial.vs_alloca_next ==>
  frag_exec_mem ctx st st' (\s. s = initial)
    (\t. w2n (abi_decode_load CALLDATALOAD p initial) <= maxn /\
      mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p initial /\
      mem_bytes_at (d+32) (w2n (abi_decode_load CALLDATALOAD p initial)*mem_sz) t.vs_memory =
        mem_bytes_at (w2n (p+32w)) (w2n (abi_decode_load CALLDATALOAD p initial)*mem_sz)
          initial.vs_call_ctx.cc_calldata /\
      abi_decode_frame d (32+maxn*mem_sz) initial t /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial) /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next)
    (\r. ?t. r = Abort Revert_abort t /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial) /\
      t.vs_memory = initial.vs_memory /\ t.vs_call_ctx = initial.vs_call_ctx /\
      t.vs_data_section = initial.vs_data_section /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next)
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bulk_shape >> strip_tac >>
  drule_all calldata_bulk_opcodes >> strip_tac >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> simp[] >> conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      ho_match_mp_tac (GEN_ALL calldata_bulk_live_prefix_safe) >>
      qexistsl_tac [`src`,`p`,`mem_sz`,`maxn`,`ei`,`dst`,`d`,`abi_sz`] >> simp[]) >>
  Cases_on `w2n (abi_decode_load CALLDATALOAD p initial) <= maxn`
  >- (`w2n (abi_decode_load CALLDATALOAD p initial)*mem_sz <= maxn*mem_sz` by
        simp[LE_MULT_RCANCEL] >>
      `d+32 < dimword (:256) /\
       w2n (abi_decode_load CALLDATALOAD p initial)*mem_sz < dimword (:256)` by decide_tac >>
      drule_all calldata_bulk_accepted_live >> strip_tac >>
      `abi_decode_frame d (32+maxn*mem_sz) initial t` by
        (irule abi_decode_frame_widen >> goal_assum (drule_at Any) >> simp[]) >>
      disj1_tac >> qexists_tac `t` >>
      gvs[instIdxIndepTheory.eval_op_inst_idx, abi_decode_frame_def] >> metis_tac[]) >>
  `maxn < w2n (abi_decode_load CALLDATALOAD p initial)` by decide_tac >>
  drule_all calldata_bulk_rejected_live >> strip_tac >>
  disj2_tac >> qexists_tac `t` >>
  simp[instIdxIndepTheory.eval_op_inst_idx]
QED

Theorem calldata_bulk_accepted_live_mod:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  d+32 < dimword (:256) /\
  w2n (abi_decode_load CALLDATALOAD p s) * mem_sz < dimword (:256) /\
  w2n (abi_decode_load CALLDATALOAD p s) <= maxn MOD dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p s /\
    mem_bytes_at (d+32) (w2n (abi_decode_load CALLDATALOAD p s)*mem_sz) t.vs_memory =
      mem_bytes_at (w2n (p+32w)) (w2n (abi_decode_load CALLDATALOAD p s)*mem_sz)
        s.vs_call_ctx.cc_calldata /\
    abi_decode_frame d (32+w2n (abi_decode_load CALLDATALOAD p s)*mem_sz) s t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bulk_phases,
    abiDecoderDynarrayPrefixTheory.abi_decode_dynarray_prefix_def,
    abiDecoderDynarrayBoundTheory.abi_decode_dynarray_end_guard_def,
    abiDecoderDynarrayPrefixTheory.abi_decode_dynarray_position_prefix_unbounded,
    abiEncoderTheory.compile_abi_dec_addr_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `abi_decode_count_guard CALLDATALOAD src maxn st = (count_op,c1)` >>
  drule_all calldata_count_guard_repeat_sequence_mod >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME p /\ eval_operand dst s1 = SOME (n2w d)` by metis_tac[] >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  `st.cs_next_var <= c1.cs_next_var` by
    (qpat_x_assum `abi_decode_count_guard _ _ _ _ = _` mp_tac >>
     simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     imp_res_tac emitted_insts_emit_op >>
     drule emitted_insts_emit_void >> strip_tac >> gvs[]) >>
  `abi_decoder_operand_live c1.cs_next_var src /\
   abi_decoder_operand_live c1.cs_next_var dst` by
    (conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  `abi_decode_load CALLDATALOAD p s1 = abi_decode_load CALLDATALOAD p s` by
    simp[abi_decode_load_def, abi_decode_source_def] >>
  drule calldata_bulk_body_live >>
  disch_then (qspecl_then [`s1`,`p`,`w2n (abi_decode_load CALLDATALOAD p s)`,`d`] mp_tac) >>
  simp[MULT_COMM] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`,`c1`] >> simp[]) >>
  qexists_tac `t` >> gvs[abi_decode_frame_def] >>
  conj_tac >- metis_tac[] >> rpt strip_tac >>
  `abi_decoder_operand_live c1.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  metis_tac[]
QED

Theorem calldata_bulk_rejected_live_mod:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\ eval_operand src s = SOME p /\
  maxn MOD dimword (:256) < w2n (abi_decode_load CALLDATALOAD p s) ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bulk_phases,
    abiDecoderDynarrayPrefixTheory.abi_decode_dynarray_prefix_def,
    abiDecoderDynarrayBoundTheory.abi_decode_dynarray_end_guard_def,
    abiDecoderDynarrayPrefixTheory.abi_decode_dynarray_position_prefix_unbounded,
    abiEncoderTheory.compile_abi_dec_addr_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `abi_decode_bulk_body dst src src CALLDATALOAD (Lit 0w) mem_sz c1 = ((),st')` >>
  drule_all calldata_count_guard_rejected_live_mod >> strip_tac >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  drule calldata_bulk_body_extends >> strip_tac >>
  qexists_tac `t` >> simp[] >> irule run_inst_seq_abort_extends >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem calldata_bulk_live_prefix_safe_mod:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\ eval_operand src s = SOME p /\
  eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  d+(32+maxn*mem_sz) < dimword (:256) /\
  d+(32+maxn*mem_sz) <= s.vs_alloca_next ==>
  !pre i post u. emitted_insts st st' = pre ++ i::post /\
    run_inst_seq pre s = OK u ==> inst_mem_below_frontier i u
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [calldata_bulk_sentinel, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_decode_count_guard CALLDATALOAD src maxn st = (count_op,c1)` >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  drule calldata_bulk_body_extends >> strip_tac >>
  `st.cs_next_var <= c1.cs_next_var` by
    (qpat_x_assum `abi_decode_count_guard _ _ _ _ = _` mp_tac >>
     simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     imp_res_tac emitted_insts_emit_op >>
     drule emitted_insts_emit_void >> strip_tac >> gvs[]) >>
  `abi_decoder_operand_live c1.cs_next_var src /\
   abi_decoder_operand_live c1.cs_next_var dst` by
    (conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  qpat_x_assum `emitted_insts st st' = _` (fn th => once_rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac calldata_prefix_safe_append >> conj_tac
  >- (ho_match_mp_tac calldata_prefix_safe_every >>
      drule calldata_count_guard_instruction_safe >> simp[]) >>
  gen_tac >> strip_tac >>
  Cases_on `w2n (abi_decode_load CALLDATALOAD p s) <= maxn MOD dimword (:256)`
  >- (drule_all calldata_count_guard_accepted_bounds >> strip_tac >>
      drule_all calldata_count_guard_repeat_sequence_mod >> strip_tac >> gvs[] >>
      `w2n (abi_decode_load CALLDATALOAD p s)*mem_sz <= maxn*mem_sz` by
        simp[LE_MULT_RCANCEL] >>
      pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      ho_match_mp_tac (GEN_ALL calldata_bulk_body_live_prefix_safe) >>
      `eval_operand src t = SOME p /\ eval_operand dst t = SOME (n2w d)` by metis_tac[] >>
      `abi_decode_load CALLDATALOAD p t = abi_decode_load CALLDATALOAD p s` by
        simp[abi_decode_load_def, abi_decode_source_def] >>
      qexistsl_tac [`src`,`p`,`mem_sz`,`dst`,`d`] >> simp[] >> decide_tac) >>
  `maxn MOD dimword (:256) < w2n (abi_decode_load CALLDATALOAD p s)` by decide_tac >>
  drule_all calldata_count_guard_rejected_live_mod >> gvs[]
QED

Theorem calldata_bulk_live_frag_mem_mod:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\ eval_operand src initial = SOME p /\
  eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  d+(32+maxn*mem_sz) < dimword (:256) /\
  d+(32+maxn*mem_sz) <= initial.vs_alloca_next ==>
  frag_exec_mem ctx st st' (\s. s = initial)
    (\t. w2n (abi_decode_load CALLDATALOAD p initial) <= maxn MOD dimword (:256) /\
      mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p initial /\
      mem_bytes_at (d+32) (w2n (abi_decode_load CALLDATALOAD p initial)*mem_sz) t.vs_memory =
        mem_bytes_at (w2n (p+32w)) (w2n (abi_decode_load CALLDATALOAD p initial)*mem_sz)
          initial.vs_call_ctx.cc_calldata /\
      abi_decode_frame d (32+maxn*mem_sz) initial t /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial) /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next)
    (\r. ?t. r = Abort Revert_abort t /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial) /\
      t.vs_memory = initial.vs_memory /\ t.vs_call_ctx = initial.vs_call_ctx /\
      t.vs_data_section = initial.vs_data_section /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next)
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bulk_shape >> strip_tac >>
  drule_all calldata_bulk_opcodes >> strip_tac >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> simp[] >> conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      ho_match_mp_tac (GEN_ALL calldata_bulk_live_prefix_safe_mod) >>
      qexistsl_tac [`src`,`p`,`mem_sz`,`maxn`,`ei`,`dst`,`d`,`abi_sz`] >> simp[]) >>
  Cases_on `w2n (abi_decode_load CALLDATALOAD p initial) <= maxn MOD dimword (:256)`
  >- (drule_all calldata_count_guard_accepted_bounds >> strip_tac >>
      `w2n (abi_decode_load CALLDATALOAD p initial)*mem_sz <= maxn*mem_sz` by
        simp[LE_MULT_RCANCEL] >>
      `d+32 < dimword (:256) /\
       w2n (abi_decode_load CALLDATALOAD p initial)*mem_sz < dimword (:256)` by decide_tac >>
      drule_all calldata_bulk_accepted_live_mod >> strip_tac >>
      `abi_decode_frame d (32+maxn*mem_sz) initial t` by
        (irule abi_decode_frame_widen >> goal_assum (drule_at Any) >> simp[]) >>
      disj1_tac >> qexists_tac `t` >>
      gvs[instIdxIndepTheory.eval_op_inst_idx, abi_decode_frame_def] >> metis_tac[]) >>
  `maxn MOD dimword (:256) < w2n (abi_decode_load CALLDATALOAD p initial)` by decide_tac >>
  drule_all calldata_bulk_rejected_live_mod >> strip_tac >>
  disj2_tac >> qexists_tac `t` >>
  simp[instIdxIndepTheory.eval_op_inst_idx]
QED

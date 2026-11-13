(* The allocation-free leaves of the owned source decoder contract: primitive
   words and bytestrings, and dynamic arrays of static elements without clamp
   (copied in bulk).  Neither allocates scratch. *)
Theory sourceOwnedLeafPtr
Ancestors
  sourcePrimitiveGasMem sourceBulkGasMem
  fragGasOriginPtr fragGasSeqPtr fragGasSeqMem venomExecProofs
  venomInstProofs calldataClampPtr exprLoweringProps rich_list fragExec
  decoderGhostFramePtr compileEnv venomInst loweringStateRelDefs venomExecSemantics
  entryDispatchPtr ghostPcTransportPtr instMemFrontier instIdxIndep
  ptrSafeRun memLocDefs unitTransformDefs contextCodegenRel codegenRel
  sourceOwnedArrayLoopPtr sourcePrimitiveReentryPtr abiDecoderSequenceReach
  decoderPrimitiveObservations decoderWorldFramePtr
  sourceBulkArrayLayout calldataBulkReentry calldataBulkUniformPtr
  abiDecoderBulkExecute abiStaticDynarrayLayout calldataTypedRobustPtr dynarrayLiveRobustPtr
  abiDecoderClampedWord abiDecoderBytesTyped abiValueEncoding
  abiDecoderCoherence sourceBytesRepresentation calldataDecodePtr abiDecoderReentry
  venomState abiDecoderBytes calldataDynOwned abiDecoderFrameCompose
  allocaFrontierBound allocaBudgetProps venomMemDefs ptrDiscipline bodyPtrDefs arithmetic

(* One concrete successful instruction, with its canonical ghost update. *)
Theorem owned_bytes_origin_step[local]:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
  ~is_terminator i.inst_opcode /\
  inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
  ptr_inst_ok D lo 0 ctx fn G tn i s /\
  step_inst_base i s = OK t ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G i t, step_taint i s t tn)
Proof
  strip_tac >>
  `gas_path_mem_edge ctx fn s 0
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    metis_tac[fragGasSeqMemTheory.straight_line_mem_edge] >>
  `gas_path_ptr_edge D lo ctx fn PG G tn s 0
    (step_prov PG G i t) (step_taint i s t tn)
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    metis_tac[fragGasSeqPtrTheory.straight_line_ptr_edge] >>
  `step_inst 0 ctx i s = OK t` by simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
  `~t.vs_halted` by metis_tac[step_preserves_halted] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G i t, step_taint i s t tn)` by
    (simp[gas_origin_ptr_edge_def] >>
     metis_tac[fragGasOriginTheory.gas_path_mem_edge_zero_origin]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  disch_then (qspec_then `[]` mp_tac) >>
  simp[cj 1 gas_origin_ptr_path_rules]
QED

Theorem owned_bytes_origin_indexed_step[local]:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb n = SOME i /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
  ~is_terminator i.inst_opcode /\
  inst_mem_below_frontier i (s with vs_inst_idx := n) /\
  inst_dload_in_section i (s with vs_inst_idx := n) /\
  ptr_inst_ok D lo 0 ctx fn G tn i (s with vs_inst_idx := n) /\
  step_inst_base i s = OK t ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s with vs_inst_idx := n,G,tn) []
    (OK (t with vs_inst_idx := SUC n),step_prov PG G i t,step_taint i s t tn)
Proof
  strip_tac >>
  `step_inst_base i (s with vs_inst_idx := n) =
     OK (t with vs_inst_idx := n)` by
    simp[step_inst_inst_idx_indep, exec_result_map_def] >>
  mp_tac (Q.INST [`s` |-> `s with vs_inst_idx := n`,
    `t` |-> `t with vs_inst_idx := n`] owned_bytes_origin_step) >> simp[]
QED

Theorem owned_bytes_indexed_continuation[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb n = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  step_inst_base i s = OK t /\ t.vs_current_bb = s.vs_current_bb /\
  (!fuel. ptr_inst_ok D lo fuel ctx fn G tn i (s with vs_inst_idx := n)) /\
  (!fuel. ptr_safe_run D lo fuel ctx fn PG (step_prov PG G i t)
    (step_taint i s t tn) (t with vs_inst_idx := SUC n)) ==>
  !fuel. ptr_safe_run D lo fuel ctx fn PG G tn (s with vs_inst_idx := n)
Proof
  strip_tac >> gen_tac >> irule ptr_safe_run_scalar_continuation >>
  qexistsl_tac [`bb`,`i`,`t with vs_inst_idx := n`] >>
  simp[step_inst_non_invoke, step_inst_inst_idx_indep, exec_result_map_def,
    ptr_safe_step_def]
QED

Theorem owned_bytes_memory_no_new_site[local]:
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  written_taint tn inst s = {} ==>
  (step_taint inst s t tn).t_mem SUBSET tn.t_mem
Proof
  strip_tac >>
  `new_site_bytes s t = {}` by
    (simp[new_site_bytes_def, pred_setTheory.EXTENSION, finite_mapTheory.FLOOKUP_DEF] >> metis_tac[]) >>
  mp_tac (Q.INST [`R` |-> `{}:num set`] step_taint_memory_bound) >> simp[]
QED

Theorem owned_bytes_run_origin_certificate:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecBytestring m) sa = ((),sb) /\
  C = 32 + 32 * ((m + 31) DIV 32) /\ C < dimword (:256) /\
  m < dimword (:256) /\
  eval_operand (Var p) s = SOME dw /\ eval_operand src s = SOME sw /\
  abi_decode_load CALLDATALOAD sw s = n2w len /\ len <= m /\
  not_fresh_at sa p /\ (!q. src = Var q ==> not_fresh_at sa q) /\
  run_inst_seq (emitted_insts sa sb) s = OK actual /\ ptr_covers G tn p s C /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  w2n dw + C <= s.vs_alloca_next /\ w2n dw + C < dimword (:256) /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?H u.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK (actual with vs_inst_idx := LENGTH sb.cs_current_insts),H,u)) /\
    ptr_covers H u p (actual with vs_inst_idx := LENGTH sb.cs_current_insts) C /\
    (!i. w2n dw <= i /\ i < w2n dw + C ==> i NOTIN u.t_mem) /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u
      (actual with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  drule calldata_bytestring_decoder_instructions >> strip_tac >>
  qabbrev_tac `v0 = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `v1 = "%" ++ toString (sa.cs_next_var + 1)` >>
  qabbrev_tac `v2 = "%" ++ toString (sa.cs_next_var + 2)` >>
  qabbrev_tac `i0 = mk_inst sa.cs_next_id CALLDATALOAD [src] [v0]` >>
  qabbrev_tac `i1 = mk_inst (sa.cs_next_id + 1) GT [Var v0; Lit (n2w m)] [v1]` >>
  qabbrev_tac `i2 = mk_inst (sa.cs_next_id + 2) ISZERO [Var v1] [v2]` >>
  qabbrev_tac `i3 = mk_inst (sa.cs_next_id + 3) ASSERT [Var v2] []` >>
  qabbrev_tac `i4 = mk_inst (sa.cs_next_id + 4) CALLDATACOPY
    [Var p;src;Lit (n2w C)] []` >>
  `emitted_insts sa sb = [i0;i1;i2;i3;i4]` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND, Abbr `i0`, Abbr `i1`,
      Abbr `i2`, Abbr `i3`, Abbr `i4`, Abbr `v0`, Abbr `v1`, Abbr `v2`] >>
  qpat_x_assum `run_inst_seq _ s = OK actual` mp_tac >>
  simp[run_inst_seq_def, AllCaseEqs()] >> strip_tac >>
  rename1 `step_inst_base i0 s = OK s1` >>
  rename1 `step_inst_base i1 s1 = OK s2` >>
  rename1 `step_inst_base i2 s2 = OK s3` >>
  rename1 `step_inst_base i3 s3 = OK s4` >>
  `?a. s1 = update_var v0 a s` by
    (qpat_x_assum `step_inst_base i0 s = OK s1` mp_tac >>
     simp[Abbr `i0`, step_inst_base_opcode_eqs, exec_read1_def, AllCaseEqs()] >>
     metis_tac[]) >>
  `?b. s2 = update_var v1 b s1` by
    (qpat_x_assum `step_inst_base i1 s1 = OK s2` mp_tac >>
     simp[Abbr `i1`, step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()] >>
     metis_tac[]) >>
  `?c. s3 = update_var v2 c s2` by
    (qpat_x_assum `step_inst_base i2 s2 = OK s3` mp_tac >>
     simp[Abbr `i2`, step_inst_base_opcode_eqs, exec_pure1_def, AllCaseEqs()] >>
     metis_tac[]) >>
  `s4 = s3` by
    (qpat_x_assum `step_inst_base i3 s3 = OK s4` mp_tac >>
     simp[Abbr `i3`, step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[]) >>
  qabbrev_tac `G1 = step_prov PG G i0 s1` >>
  qabbrev_tac `u1 = step_taint i0 s s1 tn` >>
  qabbrev_tac `G2 = step_prov PG G1 i1 s2` >>
  qabbrev_tac `u2 = step_taint i1 s1 s2 u1` >>
  qabbrev_tac `G3 = step_prov PG G2 i2 s3` >>
  qabbrev_tac `u3 = step_taint i2 s2 s3 u2` >>
  qabbrev_tac `G4 = step_prov PG G3 i3 s4` >>
  qabbrev_tac `u4 = step_taint i3 s3 s4 u3` >>
  qabbrev_tac `G5 = step_prov PG G4 i4 actual` >>
  qabbrev_tac `u5 = step_taint i4 s4 actual u4` >>
  `!k. p <> "%" ++ toString (sa.cs_next_var + k) /\
    src <> Var ("%" ++ toString (sa.cs_next_var + k))` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_ADD, ADD_COMM]) >>
  `p <> v0 /\ p <> v1 /\ p <> v2 /\
   src <> Var v0 /\ src <> Var v1 /\ src <> Var v2` by
    (qpat_assum `!k. p <> _ /\ _` (qspec_then `0` assume_tac) >>
     qpat_assum `!k. p <> _ /\ _` (qspec_then `1` assume_tac) >>
     qpat_assum `!k. p <> _ /\ _` (qspec_then `2` assume_tac) >>
     gvs[Abbr `v0`, Abbr `v1`, Abbr `v2`]) >>
  `eval_operand (Var p) s4 = SOME dw /\ eval_operand src s4 = SOME sw` by
    (Cases_on `src` >> gvs[eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]) >>
  `actual = write_memory_with_expansion (w2n dw)
     (TAKE C (DROP (w2n sw) s4.vs_call_ctx.cc_calldata ++ REPLICATE C 0w)) s4` by
    (qpat_x_assum `step_inst_base i4 s4 = OK actual` mp_tac >>
     qunabbrev_tac `i4` >>
     qpat_x_assum `eval_operand (Var p) s4 = SOME dw` mp_tac >>
     qpat_x_assum `eval_operand src s4 = SOME sw` mp_tac >>
     qpat_x_assum `C < dimword (:256)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt disch_tac >>
     fs[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def,
       wordsTheory.w2n_n2w] >> gvs[]) >>
  `op_taint u1 (Var v0) = {}` by
    (simp[Abbr `u1`, Abbr `i0`] >> irule dispatch_scalar_output_clean >> simp[]) >>
  `op_taint u2 (Var v1) = {}` by
    (simp[Abbr `u2`, Abbr `i1`] >> irule decoder_gt_literal_output_clean >> simp[]) >>
  `op_taint u3 (Var v2) = {}` by
    (simp[Abbr `u3`, Abbr `i2`] >> irule dispatch_scalar_output_clean >> simp[]) >>
  `op_taint u4 src = {}` by
    (Cases_on `src` >> fs[] >>
     simp[Abbr `u4`, Abbr `i3`, step_taint_other_output, mk_inst_def] >>
     simp[Abbr `u3`, Abbr `i2`, step_taint_other_output, mk_inst_def] >>
     simp[Abbr `u2`, Abbr `i1`, step_taint_other_output, mk_inst_def] >>
     simp[Abbr `u1`, Abbr `i0`, step_taint_other_output, mk_inst_def,
       op_taint_def]) >>
  `ptr_covers G1 u1 p s1 C` by
    (qunabbrev_tac `G1` >> qunabbrev_tac `u1` >>
     irule ptr_covers_step_frame >>
     simp[Abbr `i0`, mk_inst_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]) >>
  `ptr_covers G2 u2 p s2 C` by
    (qunabbrev_tac `G2` >> qunabbrev_tac `u2` >> irule ptr_covers_step_frame >>
     simp[Abbr `i1`, mk_inst_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]) >>
  `ptr_covers G3 u3 p s3 C` by
    (qunabbrev_tac `G3` >> qunabbrev_tac `u3` >> irule ptr_covers_step_frame >>
     simp[Abbr `i2`, mk_inst_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]) >>
  `ptr_covers G4 u4 p s4 C` by
    (qunabbrev_tac `G4` >> qunabbrev_tac `u4` >> irule ptr_covers_step_frame >>
     simp[Abbr `i3`, mk_inst_def]) >>
  `?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
     !k. k < LENGTH [i0;i1;i2;i3;i4] ==>
       get_instruction bb (LENGTH sa.cs_current_insts + k) =
         SOME (EL k [i0;i1;i2;i3;i4])` by
    (irule fn_has_code_same_block >> qexists_tac `sb` >>
     fs[Abbr `i4`]) >>
  `!D k n. ptr_inst_ok D lo k ctx fn G tn i0 (s with vs_inst_idx := n)` by
    (rpt gen_tac >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, Abbr `i0`, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       step_inst_non_invoke, step_inst_base_opcode_eqs, exec_read1_def,
       AllCaseEqs(), update_var_def] >>
     fs[allocas_from_def] >> first_assum MATCH_ACCEPT_TAC) >>
  `!D k n. ptr_inst_ok D lo k ctx fn G1 u1 i1 (s1 with vs_inst_idx := n)` by
    (rpt gen_tac >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, Abbr `i1`, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       step_inst_non_invoke, step_inst_base_opcode_eqs, exec_pure2_def,
       AllCaseEqs(), update_var_def, op_taint_def] >>
     fs[allocas_from_def, op_taint_def] >> conj_tac
     >- (Cases_on `FLOOKUP u1.t_var v0` >> gvs[] >>
         gen_tac >> Cases_on `op = Var v0` >> gvs[op_taint_def] >>
         Cases_on `op = Lit (n2w m)` >> gvs[op_taint_def]) >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     simp[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       AllCaseEqs()]) >>
  `!D k n. ptr_inst_ok D lo k ctx fn G2 u2 i2 (s2 with vs_inst_idx := n)` by
    (rpt gen_tac >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, Abbr `i2`, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       step_inst_non_invoke, step_inst_base_opcode_eqs, exec_pure1_def,
       AllCaseEqs(), update_var_def] >>
     fs[allocas_from_def, update_var_def] >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     simp[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       AllCaseEqs()]) >>
  `!D k n. ptr_inst_ok D lo k ctx fn G3 u3 i3 (s3 with vs_inst_idx := n)` by
    (rpt gen_tac >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, Abbr `i3`, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
     fs[allocas_from_def, update_var_def] >>
     simp[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       AllCaseEqs()]) >>
  `!D k n. ptr_inst_ok D lo k ctx fn G4 u4 i4 (s4 with vs_inst_idx := n)` by
    (rpt gen_tac >>
     `access_ok lo G4 fn i4 (s4 with vs_inst_idx := n)` by
       (qunabbrev_tac `i4` >> irule calldatacopy_access_ok >>
        qexistsl_tac [`n2w C`,`u4`] >>
        fs[eval_operand_def, wordsTheory.w2n_n2w, ptr_covers_def, lookup_var_def]) >>
     `taint_ok fn u4 i4 (s4 with vs_inst_idx := n)` by
       (qunabbrev_tac `i4` >> irule calldatacopy_taint_ok >>
        fs[ptr_covers_def, op_taint_def]) >>
     simp[ptr_inst_ok_def, Abbr `i4`, mk_inst_def,
       step_inst_non_invoke, step_inst_base_opcode_eqs] >>
     fs[allocas_from_def, update_var_def, eval_operand_def] >>
     simp[write_memory_with_expansion_def, write_memory_def, expand_memory_def,
       AllCaseEqs()] >> gvs[]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (actual with vs_inst_idx := LENGTH sb.cs_current_insts),G5,u5)` by
    suspend "path" >>
  qexistsl_tac [`G5`,`u5`] >>
  conj_tac >- (qpat_x_assum `!D explicit. gas_origin_ptr_path _ _ _ _` mp_tac >> simp[]) >>
  conj_tac >- suspend "coverage" >>
  conj_tac >- suspend "written" >>
  conj_tac >- suspend "variables" >>
  conj_tac >- suspend "memory" >>
  conj_tac >- suspend "storage" >>
  conj_tac >- suspend "transient" >>
  conj_tac >- suspend "immutable" >>
  suspend "backwards"
QED

Resume owned_bytes_run_origin_certificate[variables]:
  rpt strip_tac >>
  `x <> v0 /\ x <> v1 /\ x <> v2` by
    gvs[not_fresh_at_def, Abbr `v0`, Abbr `v1`, Abbr `v2`] >>
  simp[Abbr `G5`, Abbr `u5`, step_prov_other_output, step_taint_other_output,
    Abbr `i4`, mk_inst_def] >>
  simp[Abbr `G4`, Abbr `u4`, step_prov_other_output, step_taint_other_output,
    Abbr `i3`, mk_inst_def] >>
  simp[Abbr `G3`, Abbr `u3`, step_prov_other_output, step_taint_other_output,
    Abbr `i2`, mk_inst_def] >>
  simp[Abbr `G2`, Abbr `u2`, step_prov_other_output, step_taint_other_output,
    Abbr `i1`, mk_inst_def] >>
  simp[Abbr `G1`, Abbr `u1`, step_prov_other_output, step_taint_other_output,
    Abbr `i0`, mk_inst_def]
QED

Resume owned_bytes_run_origin_certificate[coverage]:
  `ptr_covers G5 u5 p actual C` by
    (qunabbrev_tac `G5` >> qunabbrev_tac `u5` >>
     irule ptr_covers_step_frame >>
     simp[Abbr `i4`, mk_inst_def, write_memory_with_expansion_def,
       write_memory_def, expand_memory_def, lookup_var_def]) >>
  fs[ptr_covers_def, lookup_var_def]
QED

Resume owned_bytes_run_origin_certificate[written]:
  gen_tac >> disch_tac >> qunabbrev_tac `u5` >> qunabbrev_tac `i4` >>
  irule calldatacopy_written_range_clean >>
  conj_tac >- (qexistsl_tac [`dw`, `n2w C`] >>
    fs[eval_operand_def, wordsTheory.w2n_n2w]) >>
  qexists_tac `sw` >> simp[]
QED

Resume owned_bytes_run_origin_certificate[storage]:
  simp[Abbr `u5`, Abbr `i4`, calldatacopy_nonmemory_taint] >>
  simp[Abbr `u4`, Abbr `i3`, step_taint_def, mk_inst_def,
    adopt_reset_def, store_taint_def, imm_taint_def] >>
  simp[Abbr `u3`, Abbr `i2`, step_taint_def, mk_inst_def,
    adopt_reset_def, store_taint_def, imm_taint_def] >>
  simp[Abbr `u2`, Abbr `i1`, step_taint_def, mk_inst_def,
    adopt_reset_def, store_taint_def, imm_taint_def] >>
  simp[Abbr `u1`, Abbr `i0`, step_taint_def, mk_inst_def,
    adopt_reset_def, store_taint_def, imm_taint_def]
QED

Resume owned_bytes_run_origin_certificate[transient]:
  simp[Abbr `u5`, Abbr `i4`, calldatacopy_nonmemory_taint] >>
  simp[Abbr `u4`, Abbr `i3`, step_taint_def, mk_inst_def,
    adopt_reset_def, store_taint_def, imm_taint_def] >>
  simp[Abbr `u3`, Abbr `i2`, step_taint_def, mk_inst_def,
    adopt_reset_def, store_taint_def, imm_taint_def] >>
  simp[Abbr `u2`, Abbr `i1`, step_taint_def, mk_inst_def,
    adopt_reset_def, store_taint_def, imm_taint_def] >>
  simp[Abbr `u1`, Abbr `i0`, step_taint_def, mk_inst_def,
    adopt_reset_def, store_taint_def, imm_taint_def]
QED

Resume owned_bytes_run_origin_certificate[immutable]:
  simp[Abbr `u5`, Abbr `i4`, calldatacopy_nonmemory_taint] >>
  simp[Abbr `u4`, Abbr `i3`, step_taint_def, mk_inst_def,
    adopt_reset_def, store_taint_def, imm_taint_def] >>
  simp[Abbr `u3`, Abbr `i2`, step_taint_def, mk_inst_def,
    adopt_reset_def, store_taint_def, imm_taint_def] >>
  simp[Abbr `u2`, Abbr `i1`, step_taint_def, mk_inst_def,
    adopt_reset_def, store_taint_def, imm_taint_def] >>
  simp[Abbr `u1`, Abbr `i0`, step_taint_def, mk_inst_def,
    adopt_reset_def, store_taint_def, imm_taint_def]
QED

Resume owned_bytes_run_origin_certificate[memory]:
  `u1.t_mem SUBSET tn.t_mem` by
    (qunabbrev_tac `u1` >> irule owned_bytes_memory_no_new_site >>
     simp[Abbr `i0`, written_taint_def, mk_inst_def, update_var_def]) >>
  `u2.t_mem SUBSET u1.t_mem` by
    (qunabbrev_tac `u2` >> irule owned_bytes_memory_no_new_site >>
     simp[Abbr `i1`, written_taint_def, mk_inst_def, update_var_def]) >>
  `u3.t_mem SUBSET u2.t_mem` by
    (qunabbrev_tac `u3` >> irule owned_bytes_memory_no_new_site >>
     simp[Abbr `i2`, written_taint_def, mk_inst_def, update_var_def]) >>
  `u4.t_mem SUBSET u3.t_mem` by
    (qunabbrev_tac `u4` >> irule owned_bytes_memory_no_new_site >>
     simp[Abbr `i3`, written_taint_def, mk_inst_def]) >>
  `u5.t_mem SUBSET u4.t_mem` by
    (qunabbrev_tac `u5` >> irule owned_bytes_memory_no_new_site >>
     simp[Abbr `i4`, written_taint_def, mk_inst_def,
       write_memory_with_expansion_def, write_memory_def, expand_memory_def]) >>
  metis_tac[pred_setTheory.SUBSET_TRANS]
QED

Resume owned_bytes_run_origin_certificate[path]:
  rpt gen_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (s1 with vs_inst_idx := LENGTH sa.cs_current_insts + 1),G1,u1)` by
    (`LENGTH sa.cs_current_insts + 1 = SUC s.vs_inst_idx` by simp[] >>
     pop_assum SUBST1_TAC >> qunabbrev_tac `G1` >> qunabbrev_tac `u1` >>
     qpat_assum `!k. k < LENGTH _ ==> _` (qspec_then `0` assume_tac) >>
     qpat_assum `!D k n. ptr_inst_ok D lo k ctx fn G tn i0 _`
       (qspecl_then [`D`,`0`,`s.vs_inst_idx`] assume_tac) >>
     irule owned_bytes_origin_step >>
     simp[Abbr `i0`, mk_inst_def, is_terminator_def,
       inst_mem_below_frontier_def, memSafeRunTheory.inst_dload_in_section_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def] >>
     fs[mk_inst_def]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s1 with vs_inst_idx := LENGTH sa.cs_current_insts + 1,G1,u1) []
    (OK (s2 with vs_inst_idx := LENGTH sa.cs_current_insts + 2),G2,u2)` by
    (`LENGTH sa.cs_current_insts + 2 = SUC (LENGTH sa.cs_current_insts + 1)` by simp[] >>
     pop_assum SUBST1_TAC >> qunabbrev_tac `G2` >> qunabbrev_tac `u2` >>
     qpat_assum `!k. k < LENGTH _ ==> _` (qspec_then `1` assume_tac) >>
     irule owned_bytes_origin_indexed_step >>
     simp[Abbr `i1`, mk_inst_def, is_terminator_def,
       inst_mem_below_frontier_def, memSafeRunTheory.inst_dload_in_section_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def] >>
     fs[mk_inst_def, update_var_def]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s2 with vs_inst_idx := LENGTH sa.cs_current_insts + 2,G2,u2) []
    (OK (s3 with vs_inst_idx := LENGTH sa.cs_current_insts + 3),G3,u3)` by
    (`LENGTH sa.cs_current_insts + 3 = SUC (LENGTH sa.cs_current_insts + 2)` by simp[] >>
     pop_assum SUBST1_TAC >> qunabbrev_tac `G3` >> qunabbrev_tac `u3` >>
     qpat_assum `!k. k < LENGTH _ ==> _` (qspec_then `2` assume_tac) >>
     irule owned_bytes_origin_indexed_step >>
     simp[Abbr `i2`, mk_inst_def, is_terminator_def,
       inst_mem_below_frontier_def, memSafeRunTheory.inst_dload_in_section_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def] >>
     fs[mk_inst_def, update_var_def]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s3 with vs_inst_idx := LENGTH sa.cs_current_insts + 3,G3,u3) []
    (OK (s4 with vs_inst_idx := LENGTH sa.cs_current_insts + 4),G4,u4)` by
    (`LENGTH sa.cs_current_insts + 4 = SUC (LENGTH sa.cs_current_insts + 3)` by simp[] >>
     pop_assum SUBST1_TAC >> qunabbrev_tac `G4` >> qunabbrev_tac `u4` >>
     qpat_assum `!k. k < LENGTH _ ==> _` (qspec_then `3` assume_tac) >>
     irule owned_bytes_origin_indexed_step >>
     simp[Abbr `i3`, mk_inst_def, is_terminator_def,
       inst_mem_below_frontier_def, memSafeRunTheory.inst_dload_in_section_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def] >>
     fs[mk_inst_def, update_var_def]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s4 with vs_inst_idx := LENGTH sa.cs_current_insts + 4,G4,u4) []
    (OK (actual with vs_inst_idx := LENGTH sa.cs_current_insts + 5),G5,u5)` by
    (`LENGTH sa.cs_current_insts + 5 = SUC (LENGTH sa.cs_current_insts + 4)` by simp[] >>
     pop_assum SUBST1_TAC >> qunabbrev_tac `G5` >> qunabbrev_tac `u5` >>
     qpat_assum `!k. k < LENGTH _ ==> _` (qspec_then `4` assume_tac) >>
     irule owned_bytes_origin_indexed_step >>
     simp[Abbr `i4`, mk_inst_def, is_terminator_def,
       inst_mem_below_frontier_def, memSafeRunTheory.inst_dload_in_section_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def] >>
     fs[mk_inst_def, update_var_def] >>
     fs[sized_source_write_range_def, eval_operand_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, wordsTheory.w2n_n2w] >>
     CASE_TAC >> simp[]) >>
  `LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + 5` by simp[] >>
  pop_assum SUBST1_TAC >>
  ntac 5 (qpat_x_assum `gas_origin_ptr_path _ _ [] _` mp_tac) >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED

Resume owned_bytes_run_origin_certificate[backwards]:
  gen_tac >> disch_tac >>
  `LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + 5` by simp[] >>
  `!fuel. ptr_safe_run D lo fuel ctx fn PG G4 u4
    (s4 with vs_inst_idx := LENGTH sa.cs_current_insts + 4)` by
    (qpat_assum `!k. k < LENGTH _ ==> _` (qspec_then `4` assume_tac) >>
     irule (Q.INST [`s` |-> `s4`, `t` |-> `actual`]
       owned_bytes_indexed_continuation) >>
     qexistsl_tac [`actual`,`bb`,`i4`] >>
     fs[ADD1, Abbr `G5`, Abbr `u5`, Abbr `i4`, mk_inst_def,
       is_terminator_def, update_var_def, write_memory_with_expansion_def,
       write_memory_def, expand_memory_def] >> gvs[]) >>
  `!fuel. ptr_safe_run D lo fuel ctx fn PG G3 u3
    (s3 with vs_inst_idx := LENGTH sa.cs_current_insts + 3)` by
    (qpat_assum `!k. k < LENGTH _ ==> _` (qspec_then `3` assume_tac) >>
     irule (Q.INST [`s` |-> `s3`] owned_bytes_indexed_continuation) >>
     qexistsl_tac [`bb`,`i3`,`s4`] >>
     fs[ADD1, Abbr `G4`, Abbr `u4`, Abbr `i3`, mk_inst_def,
       is_terminator_def, update_var_def] >> gvs[]) >>
  `!fuel. ptr_safe_run D lo fuel ctx fn PG G2 u2
    (s2 with vs_inst_idx := LENGTH sa.cs_current_insts + 2)` by
    (qpat_assum `!k. k < LENGTH _ ==> _` (qspec_then `2` assume_tac) >>
     irule (Q.INST [`s` |-> `s2`] owned_bytes_indexed_continuation) >>
     qexistsl_tac [`bb`,`i2`,`s3`] >>
     fs[ADD1, Abbr `G3`, Abbr `u3`, Abbr `i2`, mk_inst_def,
       is_terminator_def, update_var_def] >> gvs[]) >>
  `!fuel. ptr_safe_run D lo fuel ctx fn PG G1 u1
    (s1 with vs_inst_idx := LENGTH sa.cs_current_insts + 1)` by
    (qpat_assum `!k. k < LENGTH _ ==> _` (qspec_then `1` assume_tac) >>
     irule (Q.INST [`s` |-> `s1`] owned_bytes_indexed_continuation) >>
     qexistsl_tac [`bb`,`i1`,`s2`] >>
     fs[ADD1, Abbr `G2`, Abbr `u2`, Abbr `i1`, mk_inst_def,
       is_terminator_def, update_var_def] >> gvs[]) >>
  `!fuel. ptr_safe_run D lo fuel ctx fn PG G tn
    (s with vs_inst_idx := LENGTH sa.cs_current_insts)` by
    (qpat_assum `!k. k < LENGTH _ ==> _` (qspec_then `0` assume_tac) >>
     irule (Q.INST [`s` |-> `s`] owned_bytes_indexed_continuation) >>
     qexistsl_tac [`bb`,`i0`,`s1`] >>
     fs[ADD1, Abbr `G1`, Abbr `u1`, Abbr `i0`, mk_inst_def,
       is_terminator_def, update_var_def] >> gvs[]) >>
  `s with vs_inst_idx := LENGTH sa.cs_current_insts = s` by
    (qpat_assum `s.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  metis_tac[]
QED

Finalise owned_bytes_run_origin_certificate

Theorem source_owned_primitive_decoder_ptr:
  abi_decoder_coherent ce env sf ty tv /\
  ((?clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\ is_word_type ty) \/
   (?m. type_to_abi_dec_info sf ce ty = DecBytestring m)) /\
  compile_abi_decode_to_buf (Var child) childsrc CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  value_has_type tv v /\
  vyper_to_abi env ty v = SOME av /\
  mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env ty) av))
    r.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env ty) av /\
  srcpos + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
  eval_operand childsrc r = SOME (n2w srcpos) /\
  lookup_var child r = SOME (n2w e) /\ lookup_var root r = SOME (n2w d) /\
  abi_decoder_operand_live middle.cs_next_var childsrc /\
  abi_decoder_operand_live middle.cs_next_var (Var child) /\
  abi_decoder_operand_live middle.cs_next_var (Var root) /\
  ptr_covers G tn child r (type_memory_size tv) /\
  ptr_covers G tn root r outsz /\ op_taint tn childsrc = {} /\ op_prov G childsrc = NONE /\
  alloca_inv r /\ alloca_frontier_inv ctx fn site r /\
  unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP r.vs_allocas oid = SOME (base_addr,owner_cap) /\
  (oid < middle.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= e /\ e + type_memory_size tv <= base_addr + owner_cap /\
  e + type_memory_size tv < dimword (:256) /\
  (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP r.vs_allocas id = SOME (p,k) ==>
    k = 32 /\ p < dimword (:256) /\ p+32 <= r.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  fn_has_code middle end_st fn /\ fn_inst_ids_distinct fn /\
  (middle.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  end_st.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit r /\
  allocas_from lower r /\ lower <= r.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~r.vs_halted /\ r.vs_current_bb = middle.cs_current_bb /\
  r.vs_inst_idx = LENGTH middle.cs_current_insts ==>
  ?t H u.
    abi_decode_sim ctx fn r t /\
    gas_path_mem ctx fn r 0 (OK t) /\
    (!D explicit. gas_origin_ptr_path (D, lower, explicit, ctx, fn, PG) (r, G, tn) [] (OK t, H, u)) /\
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\ fresh_vars_wrt limit t /\
    val_in_memory tv v e t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory tv v e mem) /\
    abi_decode_footprint_frame [(e,type_memory_size tv)] r t /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lower t /\
    r.vs_alloca_next <= t.vs_alloca_next /\
    FLOOKUP t.vs_allocas oid = SOME (base_addr,owner_cap) /\
    (!id p k. FLOOKUP r.vs_allocas id = SOME (p,k) ==>
      FLOOKUP t.vs_allocas id = SOME (p,k)) /\
    (!id. id < middle.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP r.vs_allocas id) /\
    (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (p,k) ==>
      k = 32 /\ p < dimword (:256) /\ p+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    ptr_covers H u child t (type_memory_size tv) /\ ptr_covers H u root t outsz /\
    (!op. abi_decoder_operand_live middle.cs_next_var op ==>
      eval_operand op t = eval_operand op r) /\
    (!x. not_fresh_at middle x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lower fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lower fuel ctx fn PG G tn r) /\
    t.vs_accounts = r.vs_accounts /\ t.vs_transient = r.vs_transient /\
    t.vs_logs = r.vs_logs /\ t.vs_outcomes = r.vs_outcomes /\
    t.vs_requests = r.vs_requests /\
    t.vs_pending_deletions = r.vs_pending_deletions /\ t.vs_tx_ctx = r.vs_tx_ctx /\
    t.vs_block_ctx = r.vs_block_ctx /\ t.vs_fmp = r.vs_fmp /\
    t.vs_gas_readings = r.vs_gas_readings
Proof
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `evaluate_type env ty = SOME tv /\
   type_memory_size tv = type_memory_bytes ce ty` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `((?clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
       is_word_type ty /\ type_memory_size tv = 32) \/
    (?m. type_to_abi_dec_info sf ce ty = DecBytestring m /\
       type_memory_size tv = abi_decode_bytes_copy_size m /\ m < dimword (:256)))` by
    (qpat_x_assum `(?clamp. _ /\ is_word_type ty) \/ _` strip_assume_tac
     >- metis_tac[abi_word_type_size] >>
     drule_all coherent_source_bytes_representation >> strip_tac >>
     disj2_tac >> qexists `m` >>
     `m < dimword (:256)` by
       (mp_tac (Q.INST [`n` |-> `m`] abi_decoder_bytes_copy_size) >> decide_tac) >>
     metis_tac[]) >> (
  `type_memory_size tv < dimword (:256) /\ e < dimword (:256) /\
    srcpos < dimword (:256)` by decide_tac >>
  `not_fresh_at middle child /\ not_fresh_at middle root /\
   (!x. childsrc = Var x ==> not_fresh_at middle x)` by
    (conj_tac >- metis_tac[calldata_operand_live_not_fresh] >>
     conj_tac >- metis_tac[calldata_operand_live_not_fresh] >>
     rpt strip_tac >>
     metis_tac[calldata_operand_live_not_fresh]) >>
  `eval_operand (Var child) r = SOME (n2w e)` by simp[eval_operand_def] >>
  `?t H u.
    run_inst_seq (emitted_insts middle end_st) r = OK (t with vs_inst_idx := r.vs_inst_idx) /\
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ptr_covers H u child t (type_memory_size tv) /\
    val_in_memory tv v e t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==> val_in_memory tv v e mem) /\
    abi_decode_frame e (type_memory_size tv) r t /\ fresh_vars_wrt limit t /\
    t.vs_allocas = r.vs_allocas /\ t.vs_alloca_next = r.vs_alloca_next /\
    (!op w. (!x. op = Var x ==> not_fresh_at middle x) /\ eval_operand op r = SOME w ==>
      eval_operand op t = SOME w) /\
    (!x. not_fresh_at middle x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lower fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lower fuel ctx fn PG G tn r)` by
    (irule source_primitive_decoder_reentry_ptr >>
     metis_tac[]) >>
  `base_addr + owner_cap <= r.vs_alloca_next` by
    metis_tac[alloca_inv_def, alloca_next_valid_def] >>
  `e + type_memory_size tv <= r.vs_alloca_next` by decide_tac >>
  `gas_path_mem ctx fn r 0
     (OK ((t with vs_inst_idx := r.vs_inst_idx) with
       vs_inst_idx := LENGTH end_st.cs_current_insts))` by
    (irule source_primitive_run_gas_path_mem >>
     conj_tac >- simp[] >>
     qexistsl [`child`, `type_to_abi_dec_info sf ce ty`, `e`, `middle`,
       `childsrc`, `type_memory_size tv`] >> metis_tac[]) >>
  `gas_path_mem ctx fn r 0 (OK t)` by
    (qpat_x_assum `gas_path_mem _ _ _ _ _` mp_tac >>
     qpat_x_assum `t.vs_inst_idx = _` (fn th => simp[GSYM th])) >>
  drule decoder_primitive_code_shape >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `abi_decode_sim ctx fn r t` by
    (drule_all abi_decoder_run_sequence_reach >>
     qpat_x_assum `t.vs_inst_idx = _` (fn th => simp[GSYM th])) >>
  `!op. abi_decoder_operand_live middle.cs_next_var op ==>
    eval_operand op t = eval_operand op r` by
    (rpt strip_tac >>
     drule decoder_primitive_old_operand >>
     disch_then (qspecl_then [`t with vs_inst_idx := r.vs_inst_idx`,`r`,`op`] mp_tac) >>
     (impl_tac >- metis_tac[]) >>
     simp[eval_operand_def, lookup_var_def]) >>
  drule_all decoder_run_world_frame >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  qexistsl [`t`,`H`,`u`] >>
  pure_asm_rewrite_tac [] >>
  simp_tac bool_ss [] >>
  conj_tac >- metis_tac[abi_decode_frame_footprint] >>
  conj_tac >-
    (qpat_x_assum `alloca_inv r` mp_tac >>
     pure_asm_rewrite_tac [alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
     simp_tac bool_ss []) >>
  conj_tac >-
    (qpat_x_assum `alloca_frontier_inv ctx fn site r` mp_tac >>
     pure_asm_rewrite_tac [alloca_frontier_inv_def, remaining_alloca_budget_def] >>
     simp_tac bool_ss []) >>
  conj_tac >-
    (qpat_x_assum `allocas_from lower r` mp_tac >>
     pure_asm_rewrite_tac [allocas_from_def] >> simp_tac bool_ss []) >>
  simp_tac bool_ss [LESS_EQ_REFL] >>
  `lookup_var root t = lookup_var root r` by
    (qpat_x_assum `!op. abi_decoder_operand_live _ op ==> _` (qspec_then `Var root` mp_tac) >>
     simp[eval_operand_def]) >>
  qpat_x_assum `ptr_covers G tn root r outsz` mp_tac >>
  pure_rewrite_tac[ptr_covers_def] >>
  `FLOOKUP H root = FLOOKUP G root /\ op_taint u (Var root) = op_taint tn (Var root)` by
    metis_tac[] >>
  pure_asm_rewrite_tac[] >> simp_tac bool_ss [])
QED

Theorem source_owned_bulk_array_ptr:
  abi_decoder_coherent ce env sf (ArrayT ety (Dynamic maxn)) tv /\
  ~is_abi_dynamic ce.ce_struct_fields ety /\
  ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ety) /\
  compile_abi_decode_to_buf (Var child) childsrc CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce (ArrayT ety (Dynamic maxn))) middle = ((),end_st) /\
  value_has_type tv v /\
  vyper_to_abi env (ArrayT ety (Dynamic maxn)) v = SOME av /\
  mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env (ArrayT ety (Dynamic maxn))) av))
    r.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env (ArrayT ety (Dynamic maxn))) av /\
  srcpos + LENGTH (enc (vyper_to_abi_type env (ArrayT ety (Dynamic maxn))) av) < dimword (:256) /\
  eval_operand childsrc r = SOME (n2w srcpos) /\
  lookup_var child r = SOME (n2w e) /\ lookup_var root r = SOME (n2w d) /\
  abi_decoder_operand_live middle.cs_next_var childsrc /\
  abi_decoder_operand_live middle.cs_next_var (Var child) /\
  abi_decoder_operand_live middle.cs_next_var (Var root) /\
  ptr_covers G tn child r (type_memory_size tv) /\
  ptr_covers G tn root r outsz /\ op_taint tn childsrc = {} /\ op_prov G childsrc = NONE /\
  alloca_inv r /\ alloca_frontier_inv ctx fn site r /\
  unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP r.vs_allocas oid = SOME (base_addr,owner_cap) /\
  (oid < middle.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= e /\ e + type_memory_size tv <= base_addr + owner_cap /\
  e + type_memory_size tv < dimword (:256) /\
  (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP r.vs_allocas id = SOME (p,k) ==>
    k = 32 /\ p < dimword (:256) /\ p+32 <= r.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  fn_has_code middle end_st fn /\ fn_inst_ids_distinct fn /\
  (middle.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  end_st.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit r /\
  allocas_from lower r /\ lower <= r.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~r.vs_halted /\ r.vs_current_bb = middle.cs_current_bb /\
  r.vs_inst_idx = LENGTH middle.cs_current_insts ==>
  ?t H u.
    abi_decode_sim ctx fn r t /\
    gas_path_mem ctx fn r 0 (OK t) /\
    (!D explicit. gas_origin_ptr_path (D, lower, explicit, ctx, fn, PG) (r, G, tn) [] (OK t, H, u)) /\
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\ fresh_vars_wrt limit t /\
    val_in_memory tv v e t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory tv v e mem) /\
    abi_decode_footprint_frame [(e,type_memory_size tv)] r t /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lower t /\
    r.vs_alloca_next <= t.vs_alloca_next /\
    FLOOKUP t.vs_allocas oid = SOME (base_addr,owner_cap) /\
    (!id p k. FLOOKUP r.vs_allocas id = SOME (p,k) ==>
      FLOOKUP t.vs_allocas id = SOME (p,k)) /\
    (!id. id < middle.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP r.vs_allocas id) /\
    (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (p,k) ==>
      k = 32 /\ p < dimword (:256) /\ p+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    ptr_covers H u child t (type_memory_size tv) /\ ptr_covers H u root t outsz /\
    (!op. abi_decoder_operand_live middle.cs_next_var op ==>
      eval_operand op t = eval_operand op r) /\
    (!x. not_fresh_at middle x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lower fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lower fuel ctx fn PG G tn r) /\
    t.vs_accounts = r.vs_accounts /\ t.vs_transient = r.vs_transient /\
    t.vs_logs = r.vs_logs /\ t.vs_outcomes = r.vs_outcomes /\
    t.vs_requests = r.vs_requests /\
    t.vs_pending_deletions = r.vs_pending_deletions /\ t.vs_tx_ctx = r.vs_tx_ctx /\
    t.vs_block_ctx = r.vs_block_ctx /\ t.vs_fmp = r.vs_fmp /\
    t.vs_gas_readings = r.vs_gas_readings /\
    t.vs_allocas = r.vs_allocas /\ t.vs_alloca_next = r.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all source_bulk_array_layout >> strip_tac >>
  `evaluate_type env (ArrayT ety (Dynamic maxn)) = SOME tv` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `type_to_abi_dec_info sf ce (ArrayT ety (Dynamic maxn)) =
    DecDynArray (type_to_abi_dec_info sf ce ety) (abi_embedded_static_size ce.ce_struct_fields ety)
      (type_memory_size etv) F maxn` by
    simp[exprLoweringTheory.type_to_abi_dec_info_def] >>
  `0 < type_slot_size etv /\
   1 + maxn * type_slot_size etv < dimword (:256)` by
    (qpat_x_assum `evaluate_type env (ArrayT _ _) = _` mp_tac >>
     pure_asm_rewrite_tac [Once vyperValueTheory.evaluate_type_def] >>
     simp_tac (srw_ss()) [LET_THM, AllCaseEqs(), vyperValueTheory.type_slot_size_def]) >>
  `maxn <= maxn * type_slot_size etv` by
    (Cases_on `type_slot_size etv` >- decide_tac >> simp[MULT_SUC]) >>
  `maxn < dimword (:256)` by decide_tac >>
  `type_memory_size tv = 32 + maxn * type_memory_size etv` by
    metis_tac[valueEncodingTheory.type_memory_size_def] >>
  `LENGTH vs * type_memory_size etv <= maxn * type_memory_size etv` by
    simp[LE_MULT_RCANCEL] >>
  `32 + LENGTH vs * type_memory_size etv <= type_memory_size tv /\
   e+32 < dimword (:256) /\ LENGTH vs * type_memory_size etv < dimword (:256)` by
    decide_tac >>
  `LENGTH (enc (vyper_to_abi_type env (ArrayT ety (Dynamic maxn))) av) =
    32 + LENGTH vs * type_memory_size etv` by
    (pure_asm_rewrite_tac [listTheory.LENGTH_APPEND] >> simp_tac (srw_ss()) []) >>
  `srcpos+32 < dimword (:256) /\ srcpos < dimword (:256)` by decide_tac >>
  `mem_word_at srcpos r.vs_call_ctx.cc_calldata = n2w (LENGTH vs) /\
   mem_bytes_at (srcpos+32) (LENGTH vs * type_memory_size etv)
     r.vs_call_ctx.cc_calldata = FLAT (MAP (enc (vyper_to_abi_type env ety)) avs)` by
    (irule abiDecoderBulkTheory.static_dynarray_source_windows >>
     pure_asm_rewrite_tac [] >>
     conj_tac >-
       (qpat_x_assum `mem_bytes_at srcpos _ _ = _` mp_tac >>
        pure_rewrite_tac [vyperABITheory.vyper_to_abi_type_def] >>
        pure_asm_rewrite_tac [] >> simp_tac bool_ss []) >>
     metis_tac[]) >>
  `abi_decode_load CALLDATALOAD (n2w srcpos : bytes32) r = n2w (LENGTH vs)` by
    (qpat_x_assum `mem_word_at srcpos _ = _` mp_tac >>
     simp_tac (srw_ss()) [abiDecoderContractTheory.abi_decode_load_def,
       abiDecoderContractTheory.abi_decode_source_def, valueEncodingDefsTheory.mem_word_at_def,
       valueEncodingDefsTheory.mem_bytes_at_def, wordsTheory.w2n_n2w] >>
     `srcpos MOD dimword (:256) = srcpos` by simp[] >>
     pure_asm_rewrite_tac [] >> simp_tac bool_ss []) >>
  `eval_operand (Var child) r = SOME (n2w e)` by simp[eval_operand_def] >>
  qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
    (assume_tac o PURE_ONCE_REWRITE_RULE
      [exprLoweringTheory.type_to_abi_dec_info_def]) >>
  `compile_abi_decode_to_buf (Var child) childsrc CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray (type_to_abi_dec_info sf ce ety)
      (abi_embedded_static_size ce.ce_struct_fields ety) (type_memory_size etv) F maxn)
      middle = ((),end_st)` by metis_tac[] >>
  drule_all calldata_bulk_reentry_sequence >> strip_tac >>
  `base_addr + owner_cap <= r.vs_alloca_next` by
    metis_tac[alloca_inv_def, alloca_next_valid_def] >>
  `e + (32 + LENGTH vs * type_memory_size etv) <= r.vs_alloca_next /\
   e + (32 + LENGTH vs * type_memory_size etv) < dimword (:256)` by decide_tac >>
  `gas_path_mem ctx fn r 0
     (OK (t with vs_inst_idx := LENGTH end_st.cs_current_insts))` by
    (drule_all source_bulk_run_gas_path_mem >> simp_tac (srw_ss()) []) >>
  `not_fresh_at middle child /\ not_fresh_at middle root /\
   (!x. childsrc = Var x ==> not_fresh_at middle x)` by
    (conj_tac >- metis_tac[calldata_operand_live_not_fresh] >>
     conj_tac >- metis_tac[calldata_operand_live_not_fresh] >>
     rpt strip_tac >> metis_tac[calldata_operand_live_not_fresh]) >>
  drule_all calldata_bulk_decoder_endpoint_ptr_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `val_in_memory tv v e t.vs_memory` by
    (pure_asm_rewrite_tac [] >>
     irule static_dynarray_canonical_layout >> metis_tac[]) >>
  `!mem. mem_agree_outside u.t_mem t.vs_memory mem ==> val_in_memory tv v e mem` by
    (rpt strip_tac >> pure_asm_rewrite_tac [] >> irule clean_live_prefix_dynarray_robust >>
     metis_tac[vyperTypingTheory.all_have_type_EVERY]) >>
  `abi_decode_source_opcode CALLDATALOAD` by
    simp[abiDecoderContractTheory.abi_decode_source_opcode_def] >>
  drule_all abiDecoderBulkTheory.abi_decoder_bulk_shape >> strip_tac >>
  drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
  `inst_extends middle end_st` by
    (pure_asm_rewrite_tac [emitHelperPropsTheory.inst_extends_def,
       exprLoweringPropsTheory.emitted_insts_def] >>
     metis_tac[rich_listTheory.IS_PREFIX_APPEND, rich_listTheory.DROP_LENGTH_APPEND]) >>
  drule_all abi_decoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_x_assum `t' = _` SUBST_ALL_TAC >>
  `t.vs_labels = r.vs_labels` by
    metis_tac[ctorAbiActualObservationsTheory.ctor_actual_sequence_labels] >>
  `!op. abi_decoder_operand_live middle.cs_next_var op ==>
    eval_operand op t = eval_operand op r` by
    (rpt strip_tac >> Cases_on `op` >>
     simp_tac (srw_ss()) [eval_operand_def] >>
     metis_tac[calldata_operand_live_not_fresh]) >>
  drule_all decoder_run_world_frame >> strip_tac >>
  `alloca_inv t` by
    (qpat_x_assum `alloca_inv r` mp_tac >>
     pure_asm_rewrite_tac [alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
     simp_tac bool_ss []) >>
  `alloca_frontier_inv ctx fn site t` by
    (qpat_x_assum `alloca_frontier_inv ctx fn site r` mp_tac >>
     pure_asm_rewrite_tac [alloca_frontier_inv_def, remaining_alloca_budget_def] >>
     simp_tac bool_ss []) >>
  `allocas_from lower (t with vs_inst_idx := LENGTH end_st.cs_current_insts)` by
    (qpat_x_assum `allocas_from lower r` mp_tac >>
     simp_tac (srw_ss()) [allocas_from_def] >> pure_asm_rewrite_tac [] >> simp_tac bool_ss []) >>
  `ptr_covers H u root t outsz` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >> metis_tac[]) >>
  `abi_decode_frame e (type_memory_size tv) r t` by
    (irule abiDecoderFrameComposeTheory.abi_decode_frame_widen >>
     qexistsl [`e`,`32 + LENGTH vs * type_memory_size etv`] >>
     pure_asm_rewrite_tac [] >> decide_tac) >>
  `abi_decode_footprint_frame [(e,type_memory_size tv)] r
     (t with vs_inst_idx := LENGTH end_st.cs_current_insts)` by
    (simp_tac (srw_ss()) [GSYM abi_decode_frame_footprint,
       abiDecoderContractTheory.abi_decode_frame_def] >>
     metis_tac[abiDecoderContractTheory.abi_decode_frame_def]) >>
  qpat_x_assum `tv = _` SUBST_ALL_TAC >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  qexistsl [`t with vs_inst_idx := LENGTH end_st.cs_current_insts`,`H`,`u`] >>
  pure_asm_rewrite_tac [] >>
  simp_tac (srw_ss()) [loweringStateRelDefsTheory.fresh_vars_wrt_def,
    lookup_var_def, eval_operand_def] >>
  pure_asm_rewrite_tac [] >> simp_tac bool_ss [] >>
  conj_tac >- (qpat_assum `fresh_vars_wrt _ t` mp_tac >>
    simp_tac (srw_ss()) [loweringStateRelDefsTheory.fresh_vars_wrt_def]) >>
  simp_tac arith_ss [] >>
  conj_tac >- (qpat_x_assum `ptr_covers H u child t _` mp_tac >>
    pure_asm_rewrite_tac [] >> simp_tac arith_ss []) >>
  metis_tac[]
QED

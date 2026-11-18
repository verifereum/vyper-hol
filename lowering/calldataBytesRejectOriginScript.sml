(* A rejecting bytes count guard never reaches its copy.  The endpoint
   cursor belongs to the origin path; physical sequencing resets that cursor. *)
Theory calldataBytesRejectOrigin
Ancestors
  calldataDecodePtr calldataBytesLive fragGasCopyLoop fragGasSeqPtr
  fragGasOriginPtr fragExecMem fragExec instIdxIndep ghostPcTransportPtr
  entryDispatchPtr abiDecoderContract abiDecoderBytes abiDecoderReentry
  emitHelperProps exprLoweringProps loweringStateRelDefs compileEnv
  venomExecSemantics venomState venomInst venomInstProofs
  ptrDiscipline bodyPtrDefs unitTransformDefs contextCodegenRel codegenRel
  words arithmetic list rich_list finite_map pred_set

Theorem calldata_bytes_rejected_origin:
  compile_abi_decode_to_buf (Var child) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecBytestring maxn) st = ((),last) /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  eval_operand src initial = SOME p /\
  abi_decoder_operand_live st.cs_next_var src /\
  maxn < dimword(:256) /\
  maxn < w2n (abi_decode_load CALLDATALOAD p initial) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  allocas_from lower initial /\ ~ctx_has_dalloca ctx /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?z H u.
    run_inst_seq (emitted_insts st last) initial =
      Abort Revert_abort (z with vs_inst_idx := initial.vs_inst_idx) /\
    z.vs_returndata = [] /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
      (initial,G,tn) [] (Abort Revert_abort z,H,u))
Proof
  strip_tac >> drule calldata_bytestring_decoder_instructions >> strip_tac >>
  qabbrev_tac `v0 = "%" ++ toString st.cs_next_var` >>
  qabbrev_tac `v1 = "%" ++ toString (st.cs_next_var + 1)` >>
  qabbrev_tac `v2 = "%" ++ toString (st.cs_next_var + 2)` >>
  qabbrev_tac `i0 = mk_inst st.cs_next_id CALLDATALOAD [src] [v0]` >>
  qabbrev_tac `i1 = mk_inst (st.cs_next_id+1) GT [Var v0;Lit (n2w maxn)] [v1]` >>
  qabbrev_tac `i2 = mk_inst (st.cs_next_id+2) ISZERO [Var v1] [v2]` >>
  qabbrev_tac `i3 = mk_inst (st.cs_next_id+3) ASSERT [Var v2] []` >>
  qabbrev_tac `i4 = mk_inst (st.cs_next_id+4) CALLDATACOPY
    [Var child;src;Lit (n2w (32+32*((maxn+31) DIV 32)))] []` >>
  `emitted_insts st last = [i0;i1;i2;i3;i4]` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND, Abbr `i0`, Abbr `i1`,
      Abbr `i2`, Abbr `i3`, Abbr `i4`, Abbr `v0`, Abbr `v1`, Abbr `v2`] >>
  qabbrev_tac `s1 = update_var v0 (abi_decode_load CALLDATALOAD p initial) initial` >>
  qabbrev_tac `s2 = update_var v1 1w s1` >>
  qabbrev_tac `s3 = update_var v2 0w s2` >>
  qabbrev_tac `raw = revert_state (set_returndata [] s3)` >>
  `step_inst_base i0 initial = OK s1 /\
   step_inst_base i1 s1 = OK s2 /\
   step_inst_base i2 s2 = OK s3 /\
   step_inst_base i3 s3 = Abort Revert_abort raw` by
    (simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, Abbr `i3`,
       step_inst_base_opcode_eqs, exec_read1_def, exec_pure2_def, exec_pure1_def,
       Abbr `s1`, Abbr `s2`, Abbr `s3`, Abbr `raw`,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       abi_decode_load_def, abi_decode_source_def, w2n_n2w] >>
     fs[abi_decode_load_def, abi_decode_source_def, bool_to_word_def]) >>
  `run_inst_seq (emitted_insts st last) initial = Abort Revert_abort raw` by
    simp[run_inst_seq_def] >>
  `raw.vs_inst_idx = initial.vs_inst_idx /\ raw.vs_returndata = []` by
    simp[Abbr `raw`, Abbr `s3`, Abbr `s2`, Abbr `s1`, update_var_def,
      revert_state_def, set_returndata_def] >>
  qabbrev_tac `G1 = step_prov PG G i0 s1` >>
  qabbrev_tac `tn1 = step_taint i0 initial s1 tn` >>
  qabbrev_tac `G2 = step_prov PG G1 i1 s2` >>
  qabbrev_tac `tn2 = step_taint i1 s1 s2 tn1` >>
  qabbrev_tac `H = step_prov PG G2 i2 s3` >>
  qabbrev_tac `u = step_taint i2 s2 s3 tn2` >>
  `!D. inst_seq_ptr D lower ctx fn PG G tn [i0;i1;i2;i3;i4] initial H u` by
    suspend "ptr" >>
  `run_inst_seq_mem_ok [i0;i1;i2;i3;i4] initial` by
    suspend "mem" >>
  `?bb. lookup_block initial.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX [i0;i1;i2;i3;i4] (DROP initial.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND1, DROP_LENGTH_NIL]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS) [i0;i1;i2;i3;i4]` by
    simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, Abbr `i3`, Abbr `i4`,
      mk_inst_def, is_terminator_def] >>
  `run_inst_seq [i0;i1;i2;i3;i4] initial = Abort Revert_abort raw` by metis_tac[] >>
  drule_all run_inst_seq_abort_origin_ptr_uniform >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl [`raw with vs_inst_idx := j`, `H`, `u`] >>
  conj_tac >- simp[venom_state_component_equality] >>
  simp[] >> metis_tac[]
QED

Resume calldata_bytes_rejected_origin[ptr]:
  gen_tac >>
  simp[Once inst_seq_ptr_def] >> conj_tac >- suspend "ptr0" >>
  `~is_terminator i1.inst_opcode /\ ~is_terminator i2.inst_opcode /\
   ~is_terminator i3.inst_opcode` by
    simp[Abbr `i1`, Abbr `i2`, Abbr `i3`, mk_inst_def, is_terminator_def] >>
  simp[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def] >>
  suspend "ptrRest"
QED

Resume calldata_bytes_rejected_origin[mem]:
  simp[run_inst_seq_mem_ok_def] >>
  simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, Abbr `i3`,
    inst_mem_below_frontier_def, mk_inst_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def]
QED

Resume calldata_bytes_rejected_origin[ptr0]:
  simp[Abbr `i0`, ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
    mk_inst_def, step_inst_non_invoke, source_memory_write_ranges_def,
    source_memory_read_ranges_def, Abbr `s1`, update_var_def]
QED

Resume calldata_bytes_rejected_origin[ptrRest]:
  `op_taint tn1 (Var v0) = {}` by
    (simp[Abbr `tn1`, Abbr `i0`, dispatch_scalar_output_clean]) >>
  `op_taint tn2 (Var v1) = {}` by
    simp[Abbr `tn2`, Abbr `i1`, op_taint_def, step_taint_def,
      set_var_taint_def, out_taint_def, mk_inst_def, FLOOKUP_UPDATE,
      Abbr `s1`, eval_operand_def, lookup_var_def, update_var_def] >>
  `op_taint u (Var v2) = {}` by
    simp[Abbr `u`, Abbr `i2`, dispatch_scalar_output_clean] >>
  simp[ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
    step_inst_non_invoke, step_inst_inst_idx_indep,
    Abbr `i1`, Abbr `i2`, Abbr `i3`, mk_inst_def,
    source_memory_write_ranges_def, source_memory_read_ranges_def,
    step_inst_base_opcode_eqs, exec_pure2_def, exec_pure1_def,
    eval_operand_def, lookup_var_def, exec_result_map_def,
    Abbr `s3`, Abbr `s2`, Abbr `s1`, update_var_def,
    FLOOKUP_UPDATE] >>
  gvs[op_taint_def, allocas_from_def] >>
  rpt conj_tac
  >- (gen_tac >> Cases_on `op = Var v0` >> gvs[] >>
      Cases_on `op = Lit (n2w maxn)` >> gvs[]) >>
  metis_tac[]
QED

Finalise calldata_bytes_rejected_origin

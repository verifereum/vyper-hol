(* The rejecting count guard executes just the load, comparison, ISZERO and ASSERT. *)
Theory calldataCountGuardRejectOrigin
Ancestors
  abiDecoderGuards abiDecoderReentry abiDecoderContract fragGasCopyLoop fragGasSeqPtr
  fragGasOriginPtr fragExecMem fragExec instIdxIndep ghostPcTransportPtr
  entryDispatchPtr emitHelper emitHelperProps exprLoweringProps compileEnv
  venomExecSemantics venomState venomInst venomInstProofs ptrSafeRun
  ptrDiscipline unitTransformDefs memSafeRun contextCodegenRel codegenRel
  words arithmetic list rich_list
  finite_map pred_set

Theorem calldata_count_guard_rejected_origin:
  !src maxn sa cnt sb fn s p lower ctx PG G tn.
    abi_decode_count_guard CALLDATALOAD src maxn sa = (cnt,sb) /\
    fn_has_code sa sb fn /\ eval_operand src s = SOME p /\
    abi_decoder_operand_live sa.cs_next_var src /\
    op_taint tn src = {} /\ op_prov G src = NONE /\
    maxn MOD dimword (:256) < w2n (abi_decode_load CALLDATALOAD p s) /\
    allocas_from lower s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?z H u. run_inst_seq (emitted_insts sa sb) s =
              Abort Revert_abort (z with vs_inst_idx := s.vs_inst_idx) /\
            z.vs_returndata = [] /\
            (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
               (s,G,tn) [] (Abort Revert_abort z,H,u))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `v0 = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `v1 = "%" ++ toString (sa.cs_next_var + 1)` >>
  qabbrev_tac `v2 = "%" ++ toString (sa.cs_next_var + 2)` >>
  qabbrev_tac `i0 = mk_inst sa.cs_next_id CALLDATALOAD [src] [v0]` >>
  qabbrev_tac `i1 = mk_inst (sa.cs_next_id+1) GT [Var v0;Lit (n2w maxn)] [v1]` >>
  qabbrev_tac `i2 = mk_inst (sa.cs_next_id+2) ISZERO [Var v1] [v2]` >>
  qabbrev_tac `i3 = mk_inst (sa.cs_next_id+3) ASSERT [Var v2] []` >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ [i0;i1;i2;i3]` by
    (qpat_x_assum `abi_decode_count_guard _ _ _ _ = _` mp_tac >>
     simp[abi_decode_count_guard_def, emit_op_def, emit_void_def,
       emit_inst_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     strip_tac >>
     gvs[Abbr `i0`, Abbr `i1`, Abbr `i2`, Abbr `i3`,
       Abbr `v0`, Abbr `v1`, Abbr `v2`, APPEND_ASSOC]) >>
  `emitted_insts sa sb = [i0;i1;i2;i3]` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  qabbrev_tac `s1 = update_var v0 (abi_decode_load CALLDATALOAD p s) s` >>
  qabbrev_tac `s2 = update_var v1 1w s1` >>
  qabbrev_tac `s3 = update_var v2 0w s2` >>
  qabbrev_tac `raw = revert_state (set_returndata [] s3)` >>
  `step_inst_base i0 s = OK s1 /\
   step_inst_base i1 s1 = OK s2 /\
   step_inst_base i2 s2 = OK s3 /\
   step_inst_base i3 s3 = Abort Revert_abort raw` by suspend "steps" >>
  `run_inst_seq [i0;i1;i2;i3] s = Abort Revert_abort raw` by
    simp[run_inst_seq_def] >>
  `raw.vs_inst_idx = s.vs_inst_idx /\ raw.vs_returndata = []` by
    simp[Abbr `raw`, Abbr `s3`, Abbr `s2`, Abbr `s1`, update_var_def,
      revert_state_def, set_returndata_def] >>
  qabbrev_tac `G1 = step_prov PG G i0 s1` >>
  qabbrev_tac `tn1 = step_taint i0 s s1 tn` >>
  qabbrev_tac `G2 = step_prov PG G1 i1 s2` >>
  qabbrev_tac `tn2 = step_taint i1 s1 s2 tn1` >>
  qabbrev_tac `H = step_prov PG G2 i2 s3` >>
  qabbrev_tac `u = step_taint i2 s2 s3 tn2` >>
  `!D. inst_seq_ptr D lower ctx fn PG G tn [i0;i1;i2;i3] s H u` by
    suspend "ptr" >>
  `run_inst_seq_mem_ok [i0;i1;i2;i3] s` by
    (simp[run_inst_seq_mem_ok_def] >>
     simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, Abbr `i3`,
       inst_mem_below_frontier_def, inst_dload_in_section_def, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX [i0;i1;i2;i3] (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND1, DROP_LENGTH_NIL]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS) [i0;i1;i2;i3]` by
    simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, Abbr `i3`, mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_abort_origin_ptr_uniform >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl [`raw with vs_inst_idx := j`, `H`, `u`] >>
  conj_tac >- simp[venom_state_component_equality] >>
  simp[] >> metis_tac[]
QED

Resume calldata_count_guard_rejected_origin[steps]:
  simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, Abbr `i3`,
    step_inst_base_opcode_eqs, exec_read1_def, exec_pure2_def, exec_pure1_def,
    Abbr `s1`, Abbr `s2`, Abbr `s3`, Abbr `raw`,
    eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
    abi_decode_load_def, abi_decode_source_def, w2n_n2w] >>
  fs[abi_decode_load_def, abi_decode_source_def, bool_to_word_def]
QED

Resume calldata_count_guard_rejected_origin[ptr]:
  `op_taint tn1 (Var v0) = {}` by
    simp[Abbr `tn1`, Abbr `i0`, dispatch_scalar_output_clean] >>
  `op_taint tn2 (Var v1) = {}` by
    simp[Abbr `tn2`, Abbr `i1`, op_taint_def, step_taint_def,
      set_var_taint_def, out_taint_def, mk_inst_def, FLOOKUP_UPDATE,
      Abbr `s1`, eval_operand_def, lookup_var_def, update_var_def] >>
  `op_taint u (Var v2) = {}` by
    simp[Abbr `u`, Abbr `i2`, dispatch_scalar_output_clean] >>
  `~is_terminator i1.inst_opcode /\ ~is_terminator i2.inst_opcode /\
   ~is_terminator i3.inst_opcode` by
    simp[Abbr `i1`, Abbr `i2`, Abbr `i3`, mk_inst_def, is_terminator_def] >>
  simp[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, step_inst_non_invoke,
    Abbr `i0`, Abbr `i1`, Abbr `i2`, Abbr `i3`, mk_inst_def,
    source_memory_write_ranges_def, source_memory_read_ranges_def,
    step_inst_base_opcode_eqs, exec_read1_def, exec_pure2_def, exec_pure1_def,
    eval_operand_def, lookup_var_def, Abbr `s3`, Abbr `s2`, Abbr `s1`,
    update_var_def, FLOOKUP_UPDATE, abi_decode_load_def, abi_decode_source_def,
    w2n_n2w, bool_to_word_def, allocas_from_def, op_taint_def] >>
  fs[abi_decode_load_def, abi_decode_source_def, op_taint_def, allocas_from_def] >>
  rpt conj_tac
  >- (gen_tac >> Cases_on `op = Var v0` >> simp[] >>
      Cases_on `op = Lit (n2w maxn)` >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Finalise calldata_count_guard_rejected_origin

(* Memory-checked paths for allocation-free primitive source decoders. *)
Theory sourcePrimitiveGasMem
Ancestors
  decoderPrimitiveObservations abiDecoderReservation fragGasSeqMem fragExecMem calldataDynOwned
  stmtReasonLitFragMemory abiDecoderBytes abiDecoderClampedWord
  ctorAbiActualAlloc ctorAbiActualObservations
  abiDecoderGuards abiDecoderContract abiDecoderComposition
  abiEncoder emitHelper emitHelperProps exprLoweringProps compileEnv
  venomState venomInst venomExecSemantics instMemFrontier
  words list rich_list arithmetic

Theorem source_primitive_accesses[local]:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) di sa = ((),sb) /\
  ((?clamp. di = DecPrimWord clamp /\ sz = 32) \/
   (?n. di = DecBytestring n /\ sz = abi_decode_bytes_copy_size n)) ==>
  EVERY (\i. ~is_alloca_op i.inst_opcode /\
    i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES /\ i.inst_opcode <> GAS /\
    (!s. (\x. inst_mem_below_frontier i x) s \/
      (?id v outs. i = mk_inst id MSTORE [dst;v] outs /\ sz = 32) \/
      (?id outs. i = mk_inst id CALLDATACOPY [dst;src;Lit (n2w sz)] outs)))
    (emitted_insts sa sb)
Proof
  strip_tac >> gvs[]
  >- (Cases_on `clamp` >>
      FIRST [rename1 `IntClamp bits signed` >> Cases_on `signed`, all_tac] >>
      qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
      simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def,
        compile_abi_decode_static_def, compile_abi_clamp_basetype_def,
        compile_abi_int_clamp_def, compile_abi_bytes_clamp_def,
        comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
        emit_void_def, fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
      rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
      pure_rewrite_tac[GSYM APPEND_ASSOC] >>
      simp[DROP_LENGTH_APPEND, mk_inst_def, is_alloca_op_def,
        below_frontier_no_ranges]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  simp[abi_decode_bytes_sentinel, abi_decode_source_opcode_def,
    compile_abi_dec_addr_def, abi_decode_count_guard_def,
    abi_decode_copy_opcode_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_alloca_op_def,
    below_frontier_no_ranges]
QED

Theorem source_primitive_run_mem_ok[local]:
  compile_abi_decode_to_buf (Var child) src CALLDATALOAD (Lit 0w) (Lit 0w) di sa = ((),sb) /\
  ((?clamp. di = DecPrimWord clamp /\ sz = 32) \/
   (?n. di = DecBytestring n /\ sz = abi_decode_bytes_copy_size n)) /\
  abi_decoder_operand_live sa.cs_next_var (Var child) /\
  lookup_var child r = SOME (n2w e) /\
  e + sz <= r.vs_alloca_next /\ e + sz < dimword (:256) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) r
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule decoder_primitive_code_shape >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  drule_all source_primitive_accesses >> strip_tac >>
  `not_fresh_at sa child` by metis_tac[calldata_operand_live_not_fresh] >>
  `EVERY (\i. ~MEM child i.inst_outputs) (emitted_insts sa sb)` by
    (qpat_x_assum `(?clamp. di = _ /\ _) \/ _` strip_assume_tac >> gvs[] >>
     metis_tac[decoder_word_old_outputs, decoder_bytes_old_outputs]) >>
  irule run_inst_seq_mem_ok_of_prefix_safe >>
  reverse conj_tac >- (fs[EVERY_MEM] >> metis_tac[]) >>
  rpt strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ ~MEM child i.inst_outputs) pre /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode) pre` by
    (gvs[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
  `lookup_var child u = lookup_var child r` by
    metis_tac[ctor_actual_sequence_var_frame] >>
  `u.vs_alloca_next = r.vs_alloca_next` by
    metis_tac[abi_decode_sequence_allocation_frame] >>
  `!s. inst_mem_below_frontier i s \/
      (?id v outs. i = mk_inst id MSTORE [Var child;v] outs /\ sz = 32) \/
      (?id outs. i = mk_inst id CALLDATACOPY [Var child;src;Lit (n2w sz)] outs)` by
    (gvs[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
  pop_assum (qspec_then `u` strip_assume_tac) >> gvs[] >>
  simp[below_frontier_MSTORE, below_frontier_CALLDATACOPY,
    eval_operand_def, w2n_n2w] >> rpt strip_tac >> gvs[] >>
  `e < dimword (:256) /\ sz < dimword (:256)` by decide_tac >>
  gvs[w2n_n2w]
QED

(* No typing or source-window assumption is needed here: only the destination
   accesses touch memory. In particular, capacity zero uses the same check. *)
Theorem source_primitive_run_gas_path_mem:
  compile_abi_decode_to_buf (Var child) src CALLDATALOAD (Lit 0w) (Lit 0w) di sa = ((),sb) /\
  ((?clamp. di = DecPrimWord clamp /\ sz = 32) \/
   (?n. di = DecBytestring n /\ sz = abi_decode_bytes_copy_size n)) /\
  abi_decoder_operand_live sa.cs_next_var (Var child) /\
  lookup_var child r = SOME (n2w e) /\
  e + sz <= r.vs_alloca_next /\ e + sz < dimword (:256) /\
  fn_has_code sa sb fn /\ ~r.vs_halted /\
  r.vs_current_bb = sa.cs_current_bb /\
  r.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) r = OK actual ==>
  gas_path_mem ctx fn r 0 (OK (actual with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule decoder_primitive_code_shape >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) r` by
    (irule source_primitive_run_mem_ok >> goal_assum (drule_at Any) >> metis_tac[]) >>
  drule_all source_primitive_accesses >> strip_tac >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[FILTER_EQ_NIL] >> fs[EVERY_MEM] >> metis_tac[]) >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    gvs[inst_extends_def] >>
  drule_all fn_has_code_code >> strip_tac >>
  `lookup_block r.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP r.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all run_inst_seq_gas_path_mem >> simp[]
QED

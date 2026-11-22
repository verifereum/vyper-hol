Theory createSizeImmutableLength
Ancestors
  exprSimCopy exprLowering exprLoweringProps compileEnv context emitHelper emitHelperProps
  bufferAllocationExecution abiBufferAllocationCode immutableCopyExecution
  loweringPosts loweringStateRelDefs stateRelProj loweringHalt freshWrites
  exprSimStorageCopy stmtReasonMemory venomState venomInst venomExecSemantics
  venomMemProps valueEncodingDefs valueEncodingProps vyperTyping vyperValue
  arithmetic words list finite_map abiDecodeStaticProps

(* The later stores do not affect the first word, even for a copy whose
   constructor source and destination overlap. *)
Theorem immutable_length_tail[local]:
  !n off s. 32 <= off /\ w2n b + off + 32 * n < dimword (:256) ==>
    mload (w2n b) (immutable_transfers F ctor a b n off s) = mload (w2n b) s
Proof
  Induct >> simp[immutable_transfers_def] >> rpt strip_tac >>
  `w2n b + (off + 32) + 32 * n < dimword (:256)` by decide_tac >>
  first_x_assum (qspecl_then [`off + 32`,
    `immutable_word_transfer F ctor a b off s`] mp_tac) >> simp[] >>
  `w2n (b + n2w off) = w2n b + off` by
    (irule w2n_add_n2w_lt >> decide_tac) >>
  simp[immutable_word_transfer_def, mload_mstore_apart]
QED

Theorem immutable_length_first[local]:
  0 < n /\ w2n b + 32 * n < dimword (:256) ==>
  mload (w2n b) (immutable_transfers F ctor a b n 0 s) =
    immutable_copy_read ctor a s
Proof
  Cases_on `n` >> simp[immutable_transfers_def] >> strip_tac >>
  `w2n b + 32 + 32 * n' < dimword (:256)` by decide_tac >>
  simp[immutable_length_tail, immutable_word_transfer_def, mload_mstore_same, WORD_ADD_0]
QED

Theorem immutable_snapshot_alloc_run[local]:
  compile_alloc_buffer requested sa = (buf,sm) ==>
  ?u. run_inst_seq (emitted_insts sa sm) s = OK u /\
      eval_operand buf.buf_operand u = SOME (n2w (buffer_allocation_base s sa.cs_next_id)) /\
      copy_old_operand sm buf.buf_operand /\
      u.vs_memory = s.vs_memory /\ u.vs_data_section = s.vs_data_section /\
      !op. copy_old_operand sa op ==>
        copy_old_operand sm op /\ eval_operand op u = eval_operand op s
Proof
  strip_tac >>
  drule bufferAllocationExecutionTheory.compile_alloc_buffer_execution >>
  disch_then (qspec_then `s` strip_assume_tac) >>
  drule compile_alloc_buffer_parts >> strip_tac >> gvs[] >>
  simp[copy_old_operand_def, eval_operand_def, lookup_var_update_var] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >>
  simp[buffer_allocation_fields_def, lookup_var_def, update_var_def] >>
  gen_tac >> Cases_on `op` >>
  rw[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem immutable_snapshot_copy_load[local]:
  compile_imm_copy_to_memory ctor imm src dst n 0 sm = ((),sb) /\
  emit_op MLOAD [dst] sb = (len,sc) /\
  copy_old_operand sm src /\ copy_old_operand sm dst /\
  eval_operand src u = SOME a /\ eval_operand dst u = SOME b /\
  (ctor ==> !r. imm = SOME r ==> copy_old_operand sm r /\ eval_operand r u = SOME 0w) /\
  0 < n /\ w2n b + 32 * n < dimword (:256) /\
  sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
  run_inst_seq (emitted_insts sa sm) s = OK u /\
  run_inst_seq (emitted_insts sa sc) s = OK t ==>
  eval_operand len t = SOME (immutable_copy_read ctor a u)
Proof
  strip_tac >>
  `?z. copy_runtime_frame sm u sb z /\
       z.vs_memory = (immutable_transfers F ctor a b n 0 u).vs_memory` by
    (Cases_on `ctor` >> gvs[]
     >- metis_tac[copy_ctor_run]
     >> metis_tac[copy_runtime_run]) >>
  `eval_operand dst z = SOME b` by metis_tac[copy_runtime_frame_operand] >>
  `mload (w2n b) z = immutable_copy_read ctor a u` by
    (drule_all immutable_length_first >> simp[mload_def]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  fs[copy_runtime_frame_def] >>
  `emitted_insts sm sc = emitted_insts sm sb ++ emitted_insts sb sc` by
    metis_tac[emitted_insts_append] >>
  `sc.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sc` by
    simp[APPEND_ASSOC] >>
  `emitted_insts sa sc = emitted_insts sa sm ++ emitted_insts sm sc` by
    metis_tac[emitted_insts_append] >>
  qpat_x_assum `run_inst_seq (emitted_insts sa sc) s = OK t` mp_tac >>
  asm_rewrite_tac[GSYM APPEND_ASSOC] >>
  qpat_assum `run_inst_seq (emitted_insts sa sm) s = OK u`
    (fn th => rewrite_tac[MATCH_MP run_inst_seq_append th]) >>
  qpat_assum `run_inst_seq (emitted_insts sm sb) u = OK z`
    (fn th => rewrite_tac[MATCH_MP run_inst_seq_append th]) >>
  simp[run_inst_seq_def, step_mload_eq] >> strip_tac >>
  gvs[eval_operand_def, lookup_var_update_var]
QED

Theorem create_snapshot_code_length_word:
  vv_location vv = SOME LocCode /\
  stmt_state_rel H ctx func ce cx es s /\
  vv_holds ce cx (BaseT (BytesT (Dynamic k))) tv vv es s /\
  read_result cx tv es = (INL (BytesV bytes),es) /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) =
    SOME (BaseTV (BytesT (Dynamic k))) /\
  (ce.ce_is_ctor ==> !a. eval_operand (vv_operand vv) s = SOME a ==>
    val_in_memory (BaseTV (BytesT (Dynamic k))) (BytesV bytes) (w2n a) s.vs_memory) /\
  copy_old_operand sa (vv_operand vv) /\ local_ptrs_reserved ce sa /\
  w2n (n2w (buffer_allocation_base s sa.cs_next_id) : bytes32) +
    32 * ((type_memory_bytes ce (vv_type vv) + 31) DIV 32) < dimword (:256) /\
  compile_create_snapshot ce vv ty sa = (snap,sb) /\
  emit_op MLOAD [snap] sb = (len,sc) /\
  run_inst_seq (emitted_insts sa sc) s = OK t ==>
  eval_operand len t = SOME (n2w (LENGTH bytes))
Proof
  strip_tac >>
  `?a. eval_operand (vv_operand vv) s = SOME a /\
       immutable_holds ce cx (BaseT (BytesT (Dynamic k))) tv a es s /\
       vv_type vv = BaseT (BytesT (Dynamic k))` by
    (Cases_on `vv` >> gvs[vv_holds_def, vv_location_def, vv_operand_def, vv_type_def]) >>
  `immutable_copy_read ce.ce_is_ctor a s = n2w (LENGTH bytes)` by
    (Cases_on `ce.ce_is_ctor` >> gvs[]
     >- fs[immutable_copy_read_def, GSYM mem_word_at_eq_mload, val_in_memory_def]
     >> drule_all immutable_holds_data >>
        simp[immutable_copy_read_def, GSYM mem_word_at_def, val_in_memory_def]) >>
  qpat_x_assum `compile_create_snapshot _ _ _ _ = _` mp_tac >>
  simp[compile_create_snapshot_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  drule immutable_snapshot_alloc_run >> disch_then (qspec_then `s` strip_assume_tac) >>
  drule abiBufferAllocationCodeTheory.compile_alloc_buffer_code >> strip_tac >>
  qmatch_asmsub_abbrev_tac `compile_imm_copy_to_memory _ _ _ _ n 0 _` >>
  `0 < n` by (simp[Abbr `n`, type_memory_bytes_def] >> decide_tac) >>
  rename1 `compile_alloc_buffer _ sa = (tmp,sm)` >>
  rename1 `emit_op MLOAD [tmp.buf_operand] sb = (len,sc)` >>
  `compile_imm_copy_to_memory ce.ce_is_ctor ce.ce_imm_alloca
       (vv_operand vv) tmp.buf_operand n 0 sm = ((),sb)` by
    (Cases_on `compile_imm_copy_to_memory ce.ce_is_ctor ce.ce_imm_alloca
         (vv_operand vv) tmp.buf_operand n 0 sm` >> gvs[]) >>
  `copy_old_operand sm (vv_operand vv) /\ eval_operand (vv_operand vv) u = SOME a` by
    (first_x_assum drule >> simp[]) >>
  `ce.ce_is_ctor ==> !r. ce.ce_imm_alloca = SOME r ==>
       copy_old_operand sm r /\ eval_operand r u = SOME 0w` by
    (rpt strip_tac >>
     `copy_old_operand sa r` by
       (rw[copy_old_operand_def] >> metis_tac[local_ptrs_reserved_imm_base]) >>
     drule stmt_state_rel_immutable_base_zero >> simp[immutable_base_zero_def] >>
     first_x_assum drule >> simp[]) >>
  `immutable_copy_read ce.ce_is_ctor a u = n2w (LENGTH bytes)` by
    fs[immutable_copy_read_def, mload_def] >>
  `w2n (n2w (buffer_allocation_base s sa.cs_next_id) : bytes32) +
      32 * n < dimword (:256)` by simp[] >>
  drule_all immutable_snapshot_copy_load >> simp[]
QED

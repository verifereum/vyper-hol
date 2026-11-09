(* Finite memory-safe paths for bulk typed-copy primitives. *)
Theory typedCopyBulkPathMemory
Ancestors
  placedSequenceMemory fragGasPathMem arithmetic typedCopyPrimitiveMemory typedMemoryCopy
  context compileEnv emitHelper emitHelperProps exprLoweringProps
  fragExec fragExecMem instMemFrontier memSafeRun venomInst venomState venomExecSemantics
  valueEncoding valueEncodingProps venomMemDefs valueCopy bodyCopyMemory
  immutableMemoryFrame words list rich_list

Theorem typed_copy_dynamic_path_mem:
  compile_copy_memory_dynamic dst src len sa = ((),sb) /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
  eval_operand len s = SOME w /\
  val_in_memory tv v (w2n a) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= w2n w /\ w2n w <= type_memory_size tv /\
  w2n a + w2n w <= s.vs_alloca_next /\
  w2n d + w2n w <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. gas_path_mem ctx func s 0 (OK q) /\
      val_in_memory tv v (w2n d) q.vs_memory /\
      typed_copy_state_frame sa (w2n d) (type_memory_size tv) s q /\
      ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
      q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all typed_copy_dynamic_run_seq >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (qpat_x_assum `compile_copy_memory_dynamic _ _ _ _ = _` mp_tac >>
     simp[compile_copy_memory_dynamic_def] >> strip_tac >>
     drule emitted_insts_emit_void >> strip_tac >>
     simp[run_inst_seq_mem_ok_last, below_frontier_MCOPY,
          inst_dload_in_section_def] >> simp[mk_inst_def]) >>
  `isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    (simp[IS_PREFIX_APPEND] >> metis_tac[]) >>
  drule_all placed_sequence_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `mcopy (w2n d) (w2n a) (w2n w) s with
    vs_inst_idx := LENGTH sb.cs_current_insts` >> simp[] >>
  conj_tac >- (irule mcopy_val_in_memory >> simp[]) >>
  irule typed_copy_state_frame_subinterval >>
  qexistsl_tac [`w2n d`, `w2n w`] >> simp[typed_copy_mcopy_state_frame]
QED

Theorem typed_copy_fixed_path_mem:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
  n < dimword (:256) /\
  val_in_memory tv v (w2n a) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= n /\ n <= type_memory_size tv /\
  w2n a + n <= s.vs_alloca_next /\ w2n d + n <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. gas_path_mem ctx func s 0 (OK q) /\
      val_in_memory tv v (w2n d) q.vs_memory /\
      typed_copy_state_frame sa (w2n d) (type_memory_size tv) s q /\
      ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
      q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  Cases_on `n = 0` >> strip_tac
  >- (gvs[compile_copy_memory_def, comp_return_def] >>
      qexists_tac `s` >> simp[typed_copy_state_frame_refl] >>
      conj_tac >- (irule (cj 1 gas_path_mem_rules) >> simp[]) >>
      irule val_in_memory_relocate >> simp[] >>
      qexistsl_tac [`w2n a`, `0`, `s.vs_memory`] >> simp[mem_bytes_at_def]) >>
  `compile_copy_memory_dynamic dst src (Lit (n2w n)) sa = ((),sb)` by
    (Cases_on `n` >> gvs[compile_copy_memory_def, compile_copy_memory_dynamic_def]) >>
  irule typed_copy_dynamic_path_mem >> simp[] >>
  goal_assum (drule_at (Pat `compile_copy_memory_dynamic _ _ _ _ = _`)) >>
  qexistsl_tac [`a`, `n2w n`] >> simp[eval_operand_def, w2n_n2w, LESS_MOD]
QED

Theorem typed_copy_bytestring_no_gas[local]:
  compile_store_bytestring src dst sa = ((),sb) ==>
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  simp[compile_store_bytestring_def, compile_bytestring_copy_len_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def, LET_THM] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_APPEND1, mk_inst_def]
QED

Theorem typed_copy_bytestring_path_mem:
  compile_store_bytestring src dst sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME d /\
  mem_word_at (w2n a) s.vs_memory = n2w L /\
  32 + 32 * word_size L < dimword (:256) /\
  val_in_memory tv v (w2n a) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= 32 + 32 * word_size L /\
  32 + 32 * word_size L <= type_memory_size tv /\
  w2n a + (32 + 32 * word_size L) <= s.vs_alloca_next /\
  w2n d + (32 + 32 * word_size L) <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. gas_path_mem ctx func s 0 (OK q) /\
      val_in_memory tv v (w2n d) q.vs_memory /\
      typed_copy_state_frame sa (w2n d) (type_memory_size tv) s q /\
      ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
      q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all store_bytestring_run_exact >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule compile_store_bytestring_body_mem_ok >>
     goal_assum (drule_at (Pat `compile_store_bytestring _ _ _ = _`)) >>
     qexistsl_tac [`d`, `L`, `a`] >>
     simp[GSYM mem_word_at_eq_mload] >> metis_tac[]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    metis_tac[typed_copy_bytestring_no_gas] >>
  `isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    (simp[IS_PREFIX_APPEND] >> metis_tac[]) >>
  drule_all placed_sequence_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >> simp[] >>
  conj_tac >- (irule mcopy_val_in_memory >> simp[]) >>
  simp[typed_copy_state_frame_def] >> conj_tac
  >- gvs[venom_state_component_equality] >>
  conj_tac >- gvs[lookup_var_def] >>
  simp[typed_copy_frame_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule mem_bytes_at_mcopy_disjoint >> decide_tac) >>
  simp[mcopy_def, immutableMemoryFrameTheory.immutable_write_memory_capacity, MAX_DEF]
QED

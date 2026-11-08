(* Finite memory-safe paths for word and bytestring normalization. *)
Theory typedNormalizePrimitivePath
Ancestors
  typedNormalizeFrame typedArrayLoopPathMem stmtReasonLitFragMemory fragGasSeqMem localMemoryStorePath
  typedCopyAgreement exprLoweringProps emitHelperProps list rich_list
  exprSimBufferStore exprSimAggregateChildren exprSimProps exprSimDefs
  exprLowering compileEnv externalReturnNormalizeMem valueEncodingProps
  venomState venomInst valueCopyBytes context emitHelper valueEncoding

Theorem normalize_bytestring_window_path_mem:
  is_bytestring_type dst_ty /\ is_bytestring_type src_ty /\
  compile_store_memory_typed ce dst dst_ty src src_ty sa = ((),sb) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  mload (w2n p) s = n2w len /\
  32 + 32 * word_size len < dimword (:256) /\
  w2n p + (32 + 32 * word_size len) <= s.vs_alloca_next /\
  w2n d + (32 + 32 * word_size len) <= s.vs_alloca_next /\
  val_in_memory tv v (w2n p) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= 32 + 32 * word_size len /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. gas_path_mem ctx fn s 0 (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
      val_in_memory tv v (w2n d) q.vs_memory /\
      (!a k. a + k <= w2n d \/
          w2n d + (32 + 32 * word_size len) <= a ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s)
Proof
  strip_tac >>
  `compile_store_bytestring src dst sa = ((),sb)` by
    gvs[compile_store_memory_typed_bytes] >>
  drule_all normalize_bytestring_window_run >> strip_tac >>
  drule buffer_store_bytestring_shape >> strip_tac >>
  `compile_store_memory ce src dst dst_ty dst_ty sa = ((),sb)` by
    simp[compile_store_memory_def, is_bytestring_word_type] >>
  drule aggregate_store_memory_straight >> strip_tac >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (irule compile_store_memory_no_gas >> metis_tac[is_bytestring_word_type]) >>
  fs[same_blocks_def] >> drule_all fn_has_code_code >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qpat_x_assum `gas_path_mem _ _ _ _ _` mp_tac >> simp[] >>
  strip_tac >> qexists_tac `q` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem normalize_word_window_path_mem:
  is_word_type dst_ty /\ evaluate_type tenv dst_ty = SOME tv /\
  value_has_type tv v /\ val_in_memory tv v (w2n p) s.vs_memory /\
  compile_store_memory_typed ce dst dst_ty src src_ty sa = ((),sb) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  w2n p + 32 <= s.vs_alloca_next /\ w2n d + 32 <= s.vs_alloca_next /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. gas_path_mem ctx fn s 0 (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
      val_in_memory tv v (w2n d) q.vs_memory /\
      (!a k. a + k <= w2n d \/ w2n d + 32 <= a ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s)
Proof
  strip_tac >>
  `!x. dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all normalize_word_copy_run >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule_all typed_copy_word_mem_ok >> simp[]) >>
  drule_all normalize_word_straight >> strip_tac >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_store_memory_typed_word, emit_op_def, emit_void_def,
       emit_inst_def, fresh_id_def, fresh_var_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >> strip_tac >>
     gvs[emitted_insts_def, DROP_APPEND1, mk_inst_def, APPEND_ASSOC]) >>
  fs[same_blocks_def] >> drule_all fn_has_code_code >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qpat_x_assum `gas_path_mem _ _ _ _ _` mp_tac >> simp[] >> strip_tac >>
  qexists_tac `q` >> simp[] >>
  conj_tac
  >- (drule_all val_in_memory_word_type >>
      simp[mem_word_at_eq_mload] >> strip_tac >>
      drule_all val_in_memory_word >>
      disch_then (qspecl_then [`w2n d`,
        `(mstore (w2n d) (mload (w2n p) s) s).vs_memory`] mp_tac) >>
      simp[mstore_mem_word_at_same]) >>
  rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> simp[]
QED

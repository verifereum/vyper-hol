(* Primitive typed stores: semantics and a counted path on the same witness. *)
Theory typedCopyPrimitivePathMem
Ancestors
  typedNormalizeFrame externalReturnNormalizeMem bodyDeclMemoryCounted
  typedCopyAgreement exprSimBufferStore exprSimAggregateChildren allocaFootprint
  exprLoweringProps exprSimProps exprSimDefs loweringPosts valueEncoding
  valueEncodingProps valueEncodingProofs emitHelper compileEnv context
  venomState venomExecSemantics memSafeRun fragExecMem fragGasPathMem instMemFrontier
  words arithmetic list rich_list venomInst

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
  qpat_x_assum `sb.cs_current_insts = _` kall_tac >>
  qexists_tac `q` >> simp[] >> conj_tac
  >- (irule body_decl_zero_gas_path >> simp[] >> qexists_tac `sa` >> simp[] >>
      qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
      simp[compile_store_memory_typed_word, emit_op_def, emit_void_def,
           emit_inst_def, fresh_id_def, fresh_var_def, emit_def,
           comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      strip_tac >> gvs[same_blocks_def, emitted_insts_def, DROP_APPEND1,
                       mk_inst_def, is_terminator_def]) >>
  conj_tac
  >- (drule_all val_in_memory_word_type >>
      simp[mem_word_at_eq_mload] >> strip_tac >>
      drule_all val_in_memory_word >>
      disch_then (qspecl_then [`w2n d`,
        `(mstore (w2n d) (mload (w2n p) s) s).vs_memory`] mp_tac) >>
      simp[mstore_mem_word_at_same]) >>
  rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> simp[]
QED

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
  qexists_tac `q` >> simp[] >>
  reverse conj_tac >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  irule body_decl_zero_gas_path >> simp[] >> qexists_tac `sa` >> simp[] >>
  qpat_x_assum `compile_store_bytestring _ _ _ = _` mp_tac >>
  simp[compile_store_bytestring_def, compile_bytestring_copy_len_def,
       emit_op_def, emit_void_def, emit_inst_def, fresh_id_def,
       fresh_var_def, emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> strip_tac >>
  gvs[same_blocks_def, emitted_insts_def, DROP_APPEND1,
      mk_inst_def, is_terminator_def]
QED

(* This includes a zero-byte MCOPY: neither source nor destination is read. *)
Theorem normalize_bulk_window_path_mem:
  emit_void MCOPY [dst; src; Lit (n2w n)] sa = ((),sb) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  n < dimword (:256) /\
  (n = 0 \/ w2n p + n <= s.vs_alloca_next) /\
  (n = 0 \/ w2n d + n <= s.vs_alloca_next) /\
  val_in_memory tv v (w2n p) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= n /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. gas_path_mem ctx fn s 0 (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
      val_in_memory tv v (w2n d) q.vs_memory /\
      (!a k. a + k <= w2n d \/ w2n d + n <= a ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. lookup_var x q = lookup_var x s)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule emit_mcopy_mem_ok >> disch_then irule >>
     simp[eval_operand_def, w2n_n2w]) >>
  `run_inst_seq (emitted_insts sa sb) s =
    OK (mcopy (w2n d) (w2n p) n s)` by
    (drule buffer_emit_mcopy_run >>
     disch_then (qspecl_then [`d`, `p`, `n2w n`, `s`] mp_tac) >>
     simp[eval_operand_def, w2n_n2w]) >>
  qexists_tac `mcopy (w2n d) (w2n p) n s` >>
  conj_tac
  >- (irule body_decl_zero_gas_path >> simp[] >> qexists_tac `sa` >> simp[] >>
      qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
      simp[emit_void_def, emit_inst_def, fresh_id_def, emit_def,
           comp_bind_def, comp_ignore_bind_def, comp_return_def] >> strip_tac >>
      gvs[same_blocks_def, emitted_insts_def, DROP_APPEND1,
          mk_inst_def, is_terminator_def]) >>
  conj_tac >- (irule buffer_mcopy_encoding >> simp[]) >>
  conj_tac >- (rpt strip_tac >> irule buffer_mcopy_exterior >> simp[]) >>
  simp[buffer_mcopy_restore, mcopy_def, write_memory_with_expansion_def, lookup_var_def]
QED

Theorem normalize_empty_window_path_mem:
  compile_copy_memory dst src 0 sa = ((),sb) /\
  val_in_memory tv v p s.vs_memory /\ val_wf tv v /\
  type_memory_size tv = 0 /\ ~s.vs_halted /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_path_mem ctx fn s 0 (OK (s with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  val_in_memory tv v d s.vs_memory
Proof
  strip_tac >> gvs[compile_copy_memory_def, comp_return_def] >>
  conj_tac >- (qpat_x_assum `s.vs_inst_idx = _` (SUBST1_TAC o SYM) >>
                simp[] >> irule (cj 1 gas_path_mem_rules) >> simp[]) >>
  irule valueEncodingPropsTheory.val_in_memory_relocate >>
  simp[] >> qexistsl_tac [`s.vs_memory`, `0`, `p`] >> simp[mem_bytes_at_def]
QED

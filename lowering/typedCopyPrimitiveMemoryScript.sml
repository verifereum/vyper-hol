(* Joint execution and memory safety for typed-copy primitives. *)
Theory typedCopyPrimitiveMemory
Ancestors
  typedMemoryCopy fragExecMem instMemFrontier memSafeRun bodyCopyMemory immutableMemoryFrame
  context compileEnv emitHelper emitHelperProps exprLoweringProps
  venomExecSemantics venomInst venomState venomMemDefs
  exprSimProps valueEncoding valueEncodingProps valueEncodingProofs valueCopy
  words list rich_list finite_map arithmetic

Theorem typed_copy_empty_frag_mem:
  val_in_memory tv v off s0.vs_memory ==>
  frag_exec_mem ctx sa sa (\s. s = s0)
    (\t. val_in_memory tv v off t.vs_memory /\
         typed_copy_state_frame sa off (type_memory_size tv) s0 t)
    (\r. F)
Proof
  strip_tac >> irule frag_exec_mem_refl >> simp[]
QED

Theorem typed_copy_word_mem_ok[local]:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  is_word_type dty /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME d /\
  w2n a + 32 <= s.vs_alloca_next /\
  w2n d + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_var_def, fresh_id_def, emit_def, comp_return_def] >> strip_tac >>
  gvs[] >>
  simp[emitted_insts_def, DROP_APPEND1, run_inst_seq_mem_ok_cons,
       run_inst_seq_mem_ok_last, below_frontier_MLOAD, below_frontier_MSTORE,
       inst_dload_in_section_def, mk_inst_def, step_inst_base_opcode_eqs,
       exec_read1_def, eval_operand_def, update_var_def, lookup_var_def] >>
  rewrite_tac[GSYM mk_inst_def] >>
  simp[below_frontier_MLOAD, below_frontier_MSTORE] >>
  Cases_on `dst` >> gvs[eval_operand_def, lookup_var_def] >>
  `s' <> STRING #"%" (toString sa.cs_next_var)` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  simp[FLOOKUP_UPDATE]
QED

Theorem typed_copy_word_frag_mem:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  is_word_type dty /\ evaluate_type tenv dty = SOME tv /\
  value_has_type tv v /\ type_memory_size tv = 32 /\
  mem_word_at (w2n a) s0.vs_memory = typed_val_to_w256 tv v /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME a /\ eval_operand dst s0 = SOME d /\
  w2n a + 32 <= s0.vs_alloca_next /\
  w2n d + 32 <= s0.vs_alloca_next ==>
  frag_exec_mem ctx sa sb (\s. s = s0)
    (\t. val_in_memory tv v (w2n d) t.vs_memory /\
         typed_copy_state_frame sa (w2n d) (type_memory_size tv) s0 t) (\r. F)
Proof
  strip_tac >> drule_all typed_copy_word_run_seq >> strip_tac >>
  irule fragExecMemTheory.frag_exec_mem_run_inst_seq >>
  gvs[same_blocks_def] >> simp[] >>
  conj_tac >- (irule typed_copy_word_mem_ok >> metis_tac[]) >>
  simp[typed_copy_word_state_frame] >>
  drule_all exprSimPropsTheory.val_in_memory_word >> strip_tac >>
  simp[mstore_mem_word_at_same, GSYM mem_word_at_eq_mload]
QED

Theorem typed_copy_dynamic_frag_mem:
  compile_copy_memory_dynamic dst src len sa = ((),sb) /\
  eval_operand dst s0 = SOME d /\ eval_operand src s0 = SOME a /\
  eval_operand len s0 = SOME w /\
  val_in_memory tv v (w2n a) s0.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= w2n w /\ w2n w <= type_memory_size tv /\
  w2n a + w2n w <= s0.vs_alloca_next /\
  w2n d + w2n w <= s0.vs_alloca_next ==>
  frag_exec_mem ctx sa sb (\s. s = s0)
    (\t. val_in_memory tv v (w2n d) t.vs_memory /\
         typed_copy_state_frame sa (w2n d) (type_memory_size tv) s0 t) (\r. F)
Proof
  strip_tac >> drule_all typed_copy_dynamic_run_seq >> strip_tac >>
  irule fragExecMemTheory.frag_exec_mem_run_inst_seq >>
  gvs[same_blocks_def] >> simp[] >> conj_tac
  >- (qpat_x_assum `compile_copy_memory_dynamic _ _ _ _ = _` mp_tac >>
      simp[compile_copy_memory_dynamic_def] >> strip_tac >>
      drule emitted_insts_emit_void >> strip_tac >>
      simp[run_inst_seq_mem_ok_last, below_frontier_MCOPY]) >>
  conj_tac >- (irule mcopy_val_in_memory >> simp[]) >>
  irule typed_copy_state_frame_subinterval >>
  qexistsl_tac [`w2n d`, `w2n w`] >> simp[typed_copy_mcopy_state_frame]
QED

Theorem typed_copy_fixed_frag_mem:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s0 = SOME d /\ eval_operand src s0 = SOME a /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\ n < dimword (:256) /\
  val_in_memory tv v (w2n a) s0.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= n /\ n <= type_memory_size tv /\
  w2n a + n <= s0.vs_alloca_next /\ w2n d + n <= s0.vs_alloca_next ==>
  frag_exec_mem ctx sa sb (\s. s = s0)
    (\t. val_in_memory tv v (w2n d) t.vs_memory /\
         typed_copy_state_frame sa (w2n d) (type_memory_size tv) s0 t) (\r. F)
Proof
  Cases_on `n = 0` >> strip_tac
  >- (gvs[compile_copy_memory_def, comp_return_def] >>
      irule frag_exec_mem_refl >> simp[] >>
      irule val_in_memory_relocate >> simp[] >>
      qexistsl_tac [`w2n a`, `0`, `s0.vs_memory`] >> simp[mem_bytes_at_def]) >>
  `compile_copy_memory_dynamic dst src (Lit (n2w n)) sa = ((),sb)` by
    (Cases_on `n` >> gvs[compile_copy_memory_def, compile_copy_memory_dynamic_def]) >>
  irule typed_copy_dynamic_frag_mem >> simp[] >>
  goal_assum (drule_at (Pat `compile_copy_memory_dynamic _ _ _ _ = _`)) >>
  qexistsl_tac [`a`, `n2w n`] >> simp[eval_operand_def, w2n_n2w, LESS_MOD]
QED

Theorem typed_copy_bytestring_frag_exact_mem:
  compile_store_bytestring src dst sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME a /\ eval_operand dst s0 = SOME d /\
  mem_word_at (w2n a) s0.vs_memory = n2w L /\
  32 + 32 * word_size L < dimword (:256) /\
  val_in_memory tv v (w2n a) s0.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= 32 + 32 * word_size L /\
  32 + 32 * word_size L <= type_memory_size tv /\
  w2n a + (32 + 32 * word_size L) <= s0.vs_alloca_next /\
  w2n d + (32 + 32 * word_size L) <= s0.vs_alloca_next ==>
  frag_exec_mem ctx sa sb (\s. s = s0)
    (\t. val_in_memory tv v (w2n d) t.vs_memory /\
         typed_copy_state_frame sa (w2n d) (type_memory_size tv) s0 t) (\r. F)
Proof
  strip_tac >> drule_all store_bytestring_run_exact >> strip_tac >>
  irule fragExecMemTheory.frag_exec_mem_run_inst_seq >>
  gvs[same_blocks_def] >> simp[] >> conj_tac
  >- (irule compile_store_bytestring_body_mem_ok >>
      goal_assum (drule_at (Pat `compile_store_bytestring _ _ _ = _`)) >>
      qexistsl_tac [`d`, `L`, `a`] >>
      simp[GSYM mem_word_at_eq_mload] >> metis_tac[]) >>
  conj_tac >- (irule mcopy_val_in_memory >> simp[]) >>
  simp[typed_copy_state_frame_def] >> conj_tac
  >- gvs[venom_state_component_equality] >>
  conj_tac >- gvs[lookup_var_def] >>
  simp[typed_copy_frame_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule mem_bytes_at_mcopy_disjoint >>
      decide_tac) >>
  simp[mcopy_def, immutableMemoryFrameTheory.immutable_write_memory_capacity, MAX_DEF]
QED

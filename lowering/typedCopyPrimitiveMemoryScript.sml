(* Joint execution and memory safety for typed-copy primitives. *)
Theory typedCopyPrimitiveMemory
Ancestors
  typedMemoryCopy fragExecMem instMemFrontier memSafeRun
  context compileEnv emitHelper emitHelperProps exprLoweringProps
  venomExecSemantics venomInst venomState venomMemDefs
  exprSimProps valueEncoding valueEncodingProps valueEncodingProofs words list rich_list finite_map arithmetic

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

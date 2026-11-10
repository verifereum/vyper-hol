Theory aggregateCountedStoreShapeGeneral
Ancestors
  exprSimAbiGasBridge context compileEnv vyperAST venomExecSemantics
  emitHelper emitHelperProps pred_set list rich_list fragExec venomInst exprLoweringProps

Theorem aggregate_typed_sarray_counted_shape:
  !ce dst src n sa sb.
  compile_state_ok sa /\
  compile_copy_sarray_typed ce (Var dst) (BaseT (UintT 256))
    (Var src) (TupleT []) n sa = ((),sb) ==>
  frag_gas_free sa sb /\ sb.cs_current_insts = [] /\
  LENGTH (emitted_blocks sa sb) = 3
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, type_memory_bytes_def,
       is_word_type_def] >>
  simp[Once compile_store_memory_typed_def, is_word_type_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_label_def, fresh_var_def, fresh_id_def,
       emit_inst_def, emit_op_def, emit_void_def, emit_def, new_block_def] >>
  strip_tac >> gvs[] >>
  reverse conj_tac >- simp[emitted_blocks_def] >>
  rewrite_tac[frag_gas_free_def, frag_code_def] >>
  simp[emitted_blocks_def, emitted_insts_def] >>
  simp[mk_inst_def, fresh_label_output_inj] >>
  simp[arithmeticTheory.ADD1, mk_inst_def, fresh_label_output_inj] >>
  once_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND] >>
  simp[mk_inst_def] >>
  simp[SF ETA_ss, fresh_label_output_inj] >>
  fs[compile_state_ok_def, bound_labels_def, IN_DISJOINT] >>
  rpt conj_tac >> spose_not_then assume_tac >> gvs[] >>
  imp_res_tac fresh_label_output_inj >> gvs[] >>
  qpat_x_assum `!x. _` (qspec_then `sa.cs_current_bb` mp_tac) >>
  simp[] >> metis_tac[fresh_label_output_in_future,
                     arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.LESS_EQ_ADD]
QED

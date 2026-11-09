Theory exprSimAbiEncodeArgsBridgeAudit
Ancestors
  exprSimAbiEncodeArgsMaterializePath exprLowering context compileEnv vyperAST

Theorem zero_array_storage_materialize_empty_exit:
  (SND (compile_materialize_vv ce (ArrayT (BaseT (UintT 256)) (Fixed 0))
    (LocatedValue (ArrayT (BaseT (UintT 256)) (Fixed 0))
      (mk_ptr (Lit 0w) LocStorage)) sm)).cs_current_insts = []
Proof
  simp[compile_materialize_vv_def, type_memory_bytes_def,
       unwrap_value_def, is_word_type_def, is_bytestring_type_def,
       compile_ensure_in_memory_def, compile_alloc_buffer_def,
       compile_storage_to_memory_def, compile_store_memory_def,
       compile_copy_memory_def, compile_word_copy_loop_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def] >>
  simp[mk_ptr_def, word_scale_def, compile_ptr_load_def, compile_ptr_store_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       emitHelperTheory.emit_inst_def, fresh_var_def, fresh_id_def,
       fresh_label_def, new_block_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED

Theorem empty_prefix_allows_phi_suffix:
  sm.cs_current_insts = [] ==>
  fn_has_code sm sm
    (fn with fn_blocks :=
      [<| bb_label := sm.cs_current_bb;
          bb_instructions := [mk_inst 0 PHI [] []] |>]) /\
  lookup_block sm.cs_current_bb
    (fn with fn_blocks :=
      [<| bb_label := sm.cs_current_bb;
          bb_instructions := [mk_inst 0 PHI [] []] |>]).fn_blocks =
    SOME <| bb_label := sm.cs_current_bb;
            bb_instructions := [mk_inst 0 PHI [] []] |> /\
  phi_prefix_length [mk_inst 0 PHI [] []] = 1
Proof
  simp[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def,
       venomInstTheory.lookup_block_def, listTheory.FIND_thm,
       venomExecSemanticsTheory.phi_prefix_length_def, venomInstTheory.mk_inst_def]
QED

Theorem zero_tuple_physical_candidate:
  evaluate_type tenv (TupleT []) = SOME (TupleTV []) /\
  vyperTypeSystem$well_formed_type tenv (TupleT []) /\
  value_has_type (TupleTV []) (ArrayV (TupleV [])) /\
  val_wf (TupleTV []) (ArrayV (TupleV [])) /\
  ~is_word_type (TupleT []) /\
  type_memory_bytes ce (TupleT []) = 0 /\
  type_memory_size (TupleTV []) = 0
Proof
  simp[vyperValueTheory.evaluate_type_def,
       vyperTypeSystemTheory.well_formed_type_def,
       vyperTypingTheory.value_has_type_def,
       valueEncodingTypingTheory.value_has_type_val_wf,
       vyperValueTheory.type_slot_size_def, wordsTheory.dimword_def,
       is_word_type_def, type_memory_bytes_def,
       valueEncodingTheory.type_memory_size_def]
QED

Theorem pop_tail_mutates:
  exprs_can_mutate ce [Pop (BaseT (UintT 256)) (NameTarget "xs")]
Proof
  simp[expr_can_mutate_def]
QED

Theorem pop_tail_entry_nonphi:
  sm.cs_current_insts = [] ==>
  (HD (SND (compile_abi_encode_args compile_expr
    (ce with ce_vars := FEMPTY)
    [Pop (BaseT (UintT 256)) (NameTarget "xs")] sm)).cs_current_insts).
    inst_opcode = MLOAD
Proof
  simp[compile_abi_encode_args_def, expr_type_def, is_word_type_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[Once compile_expr_def] >>
  simp[compile_get_target_ptr_def, finite_mapTheory.FLOOKUP_EMPTY,
       expr_type_def, compile_dynarray_pop_def, word_scale_def,
       elem_size_in_location_def, is_slot_addressed_def,
       type_memory_bytes_def, compile_ptr_load_def, compile_ptr_store_def,
       unwrap_value_def, is_word_type_def, mk_ptr_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       emitHelperTheory.emit_inst_def, fresh_var_def, fresh_id_def, emit_def,
       venomInstTheory.mk_inst_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED

Theorem loop_exit_may_alias_start:
  let si = sm with <| cs_next_var := 0; cs_next_id := 0; cs_next_label := 0;
                     cs_current_bb := "@wcopy_exit_2";
                     cs_current_insts := []; cs_blocks := [] |> in
  let sf = SND (compile_word_copy_loop (Lit 0w) (Lit 32w) 0
                  LocStorage LocMemory F si) in
  fn_has_code si sf (fn with fn_blocks := sf.cs_blocks) /\
  fn_inst_ids_distinct (fn with fn_blocks := sf.cs_blocks) /\
  si.cs_current_bb = sf.cs_current_bb /\
  ~frag_gas_free si sf
Proof
  simp[compile_word_copy_loop_def, word_scale_def,
       compile_ptr_load_def, compile_ptr_store_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       emitHelperTheory.emit_inst_def, fresh_var_def, fresh_id_def,
       fresh_label_def, fresh_label_output_def, new_block_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  EVAL_TAC >> conj_tac
  >- (rpt strip_tac >> gvs[] >> EVAL_TAC) >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[]
QED

(* Mutation is a syntactic overapproximation on malformed builtin arities.
   This is not a source-valid candidate. *)
Theorem mutating_syntax_can_compile_without_entry:
  let e = TypeBuiltin (BaseT (UintT 256)) MaxValue (BaseT (UintT 256))
            [Pop (BaseT (UintT 256)) (NameTarget "xs")] in
  exprs_can_mutate ce [e] /\
  SND (compile_abi_encode_args compile_expr ce [e] si) = si
Proof
  simp[expr_can_mutate_def, compile_abi_encode_args_def,
       expr_type_def, is_word_type_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  simp[Once compile_expr_def] >>
  simp[compile_expr_def, compile_type_builtin_dispatch_body_def,
       unwrap_value_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[type_bounds_def, is_signed_type_def, expr_type_def, unwrap_value_def,
       comp_bind_def, comp_return_def]
QED

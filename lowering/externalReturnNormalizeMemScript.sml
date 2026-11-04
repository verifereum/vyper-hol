Theory externalReturnNormalizeMem
Ancestors
  typedCopyAgreement context compileEnv emitHelper fragExecMem instMemFrontier
  venomExecSemantics venomState venomInst exprLoweringProps words exprSim
  vfmConstants externalReturnBounds valueEncoding vyperTypeSystem vyperValue

Theorem typed_copy_word_mem_ok:
  is_word_type dst_ty /\
  compile_store_memory_typed cenv dst dst_ty src src_ty sa = ((), sb) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  w2n p + 32 <= s.vs_alloca_next /\
  w2n d + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_store_memory_typed_word, emit_op_def, emit_void_def,
       emit_inst_def, fresh_id_def, fresh_var_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >> strip_tac >>
  gvs[emitted_insts_def, rich_listTheory.DROP_APPEND1,
      run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last,
      below_frontier_MLOAD, below_frontier_MSTORE, mk_inst_def,
      step_inst_base_def, exec_read1_def, eval_operands_def,
      eval_operand_def, lookup_var_def, update_var_def] >>
  simp[GSYM mk_inst_def, below_frontier_MLOAD, below_frontier_MSTORE] >>
  Cases_on `dst` >> gvs[eval_operand_def, lookup_var_def,
    finite_mapTheory.FLOOKUP_UPDATE, not_fresh_at_def]
QED

(* Diagnostic only: live expression bytes do not include copy padding.
   This is not a counterexample to the external-frame theorem. *)
Theorem bytestring_live_window_not_padded[local]:
  !s:venom_state.
    let t = BaseTV (BytesT (Dynamic 1));
        v = BytesV [0w];
        s' = s with vs_alloca_next := 33
    in w2n (0w:bytes32) + val_footprint t v <= s'.vs_alloca_next /\
       ~(w2n (0w:bytes32) + val_store_size t v <= s'.vs_alloca_next)
Proof
  simp[val_footprint_def, val_store_size_def, word_size_def]
QED

Theorem typed_copy_child_window[local]:
  val_wf child_tv child_v /\
  (off:num) + type_memory_size child_tv <= type_memory_size parent_tv /\
  baddr + type_memory_size parent_tv <= frontier ==>
  baddr + off + val_store_size child_tv child_v <= frontier
Proof
  strip_tac >> drule val_store_size_le >> decide_tac
QED

Theorem normalized_bytes_tuple_dispatch[local]:
  acyclic_struct_metadata cenv.ce_struct_fields ==>
  compile_store_memory_typed cenv dst
    (TupleT [BaseT (BytesT (Dynamic 2))]) src
    (TupleT [BaseT (BytesT (Dynamic 1))]) =
  compile_typed_copy_fields cenv dst src
    [BaseT (BytesT (Dynamic 2))] [BaseT (BytesT (Dynamic 1))] 0 0
Proof
  simp[compile_store_memory_typed_valid, is_word_type_def,
       is_bytestring_type_def]
QED

Theorem normalized_bytes_tuple_window[local]:
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx (TupleT [BaseT (BytesT (Dynamic 1))])
    sa sb es (ArrayV (TupleV [BytesV [0w]])) op s ==>
  ?p. eval_operand op s = SOME p /\
    w2n p + val_store_size (BaseTV (BytesT (Dynamic 1))) (BytesV [0w])
      <= s.vs_alloca_next
Proof
  strip_tac >>
  `evaluate_type (get_tenv cx) (TupleT [BaseT (BytesT (Dynamic 1))]) =
    SOME (TupleTV [BaseTV (BytesT (Dynamic 1))])` by
    (simp[evaluate_type_def, type_slot_size_def, dimword_def] >> EVAL_TAC) >>
  `~is_word_type (TupleT [BaseT (BytesT (Dynamic 1))])` by
    simp[is_word_type_def] >>
  drule_all expr_val_at_frontier >>
  simp[evaluate_type_def, is_word_type_def, val_footprint_def,
       type_memory_size_def, word_size_def, val_store_size_def]
QED

Theorem normalized_bytes_tuple_typing[local]:
  type_widens_to tenv (TupleT [BaseT (BytesT (Dynamic 1))])
    (TupleT [BaseT (BytesT (Dynamic 2))])
Proof
  EVAL_TAC >> simp[dimword_def, type_slot_size_def, word_size_def]
QED

Theorem normalized_bytes_tuple_layout[local]:
  type_memory_bytes cenv (TupleT [BaseT (BytesT (Dynamic 1))]) = 64 /\
  type_memory_bytes cenv (TupleT [BaseT (BytesT (Dynamic 2))]) = 64 /\
  type_memory_size (TupleTV [BaseTV (BytesT (Dynamic 1))]) = 64 /\
  val_store_size (BaseTV (BytesT (Dynamic 2))) (BytesV [0w]) = 64 /\
  (~is_word_type (TupleT [BaseT (BytesT (Dynamic 2))]) /\
   ~(is_bytestring_type (TupleT [BaseT (BytesT (Dynamic 2))]) /\
     is_bytestring_type (TupleT [BaseT (BytesT (Dynamic 1))])) /\
   TupleT [BaseT (BytesT (Dynamic 1))] <>
     TupleT [BaseT (BytesT (Dynamic 2))])
Proof
  simp[type_memory_bytes_def, type_memory_size_def, val_store_size_def,
       word_size_def, is_word_type_def, is_bytestring_type_def]
QED

Theorem normalized_bytes_tuple_field[local]:
  compile_typed_copy_fields cenv dst src
    [BaseT (BytesT (Dynamic 2))] [BaseT (BytesT (Dynamic 1))] 0 0 =
  compile_store_bytestring src dst
Proof
  simp[Once compile_store_memory_typed_def, compile_with_byte_offset_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  simp[compile_store_memory_typed_bytes, is_bytestring_type_def] >>
  simp[Once compile_store_memory_typed_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, FUN_EQ_THM] >>
  gen_tac >> pairarg_tac >> simp[]
QED

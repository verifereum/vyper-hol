(* Producer-local capacity probe: the literal temporary is sized by its
   actual byte length (one), not by the annotated dynamic-bytes bound (64). *)
Theory assignBasePtrLiteralSource
Ancestors bodyPtrDefs exprLowering exprLoweringProps exprSimAlloc
  allocationPtr fragGasSeqPtr context emitHelper compileEnv list words
  vyperAST vyperTyping

Theorem assign_base_ptr_one_byte_lowering:
  !cenv ty sa.
    lower_value compile_expr cenv ty
      (Literal (BaseT (BytesT (Dynamic 64))) (BytesL [1w])) sa =
    (do buf <- compile_bytelike_literal [1w] 1;
        return buf.buf_operand
     od) sa
Proof
  rpt gen_tac >> simp[lower_value_def, Once compile_expr_def, compile_literal_vv_def,
       expr_type_def, comp_bind_def, comp_return_def] >>
  Cases_on `compile_bytelike_literal [1w] 1 sa` >>
  simp[unwrap_value_def, base_ptr_def, as_ptr_val_def,
       is_word_type_def, comp_return_def]
QED

Theorem assign_base_ptr_one_byte_buffer_size:
  !cenv.
    type_memory_bytes cenv
      (lowered_value_type cenv
        (Literal (BaseT (BytesT (Dynamic 64))) (BytesL [1w]))) = 64
Proof
  gen_tac >> EVAL_TAC
QED

Theorem assign_base_ptr_one_byte_initialization:
  compile_bytelike_literal [1w] 1 =
    do buf <- compile_alloc_buffer 64;
       emit_void MSTORE [buf.buf_operand; Lit 1w];
       dst <- emit_op ADD [buf.buf_operand; Lit 32w];
       emit_void MSTORE [dst; Lit (n2w (2 ** 248))];
       return buf
    od
Proof
  `word_of_bytes T (0w:bytes32)
      ((1w:word8)::REPLICATE 31 0w) = n2w (2 ** 248)` by
    (EVAL_TAC >> simp[w2n_n2w, dimword_def]) >>
  simp[compile_bytelike_literal_def, compile_store_byte_chunks_def,
       TAKE_def, DROP_def, TAKE_LENGTH_TOO_LONG, comp_ignore_bind_def,
       comp_bind_assoc] >>
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def] >>
  gen_tac >> rpt pairarg_tac >> gvs[comp_bind_def, comp_return_def]
QED

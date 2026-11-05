Theory bodyPtrPopGlobalStatements
Ancestors
  bodyPtrPopGlobalFields bodyPtrPopGlobalInternal bodyPtrPopStructLegality
  exprLowering stmtLowering compileEnv vyperAST context
Libs monadsyntax

Theorem pop_global_rhs_compiled:
  compile_expr pop_global_body_env pop_struct_ty
    (TopLevelName pop_struct_ty (NONE,"B")) =
    comp_return (LocatedValue pop_struct_ty (mk_ptr (Lit 4w) LocStorage))
Proof
  simp[FUN_EQ_THM, Once compile_expr_def, pop_global_body_global_B,
       expr_type_def, comp_return_def]
QED

Theorem pop_global_target_compiled:
  compile_get_target_ptr compile_expr pop_global_body_env pop_struct_root =
    comp_return (Lit 0w,SOME LocStorage,SOME (ValPT pop_struct_ty))
Proof
  simp[pop_struct_root_def, compile_get_target_ptr_def,
       pop_global_body_global_A, pop_global_body_global_A_hashmap,
       pop_global_body_global_A_type]
QED

Theorem pop_global_rhs_unwrap:
  unwrap_value pop_global_body_env
    (LocatedValue pop_struct_ty (mk_ptr (Lit 4w) LocStorage)) =
  do buf <- compile_alloc_buffer 128;
     compile_storage_to_memory (Lit 4w) buf.buf_operand 4;
     return buf.buf_operand od
Proof
  simp[unwrap_value_def, pop_struct_ty_def, is_word_type_def,
       mk_ptr_def, pop_global_body_struct_bytes,
       contextTheory.compile_ensure_in_memory_def] >>
  simp[FUN_EQ_THM, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  gen_tac >> pairarg_tac >> simp[] >>
  Cases_on `compile_storage_to_memory (Lit 4w) buf_op_alloc.buf_operand 4 cs'` >> simp[]
QED

Theorem pop_global_assignment_boundary:
  compile_stmt pop_global_body_env NoLoop (BaseT (UintT 256))
    (Assign (BaseTarget pop_struct_root) (TopLevelName pop_struct_ty (NONE,"B"))) =
  do buf <- compile_alloc_buffer 128;
     compile_storage_to_memory (Lit 4w) buf.buf_operand 4;
     compile_memory_to_storage buf.buf_operand (Lit 0w) 4;
     return () od
Proof
  simp[Once compile_stmt_def, expr_type_def, has_length_word_def,
       is_empty_value_expr_def, pop_struct_ty_def, is_bytestring_type_def] >>
  rewrite_tac[GSYM pop_struct_ty_def, pop_global_rhs_compiled,
              pop_global_target_compiled] >>
  simp[FUN_EQ_THM, comp_ignore_bind_def, comp_bind_def, comp_return_def,
       pop_global_rhs_unwrap, vv_location_def, mk_ptr_def,
       lowered_value_type_def] >>
  rewrite_tac[GSYM mk_ptr_def, pop_global_rhs_unwrap,
              pop_global_body_struct_bytes, expr_type_def] >>
  simp[pop_struct_ty_def, is_word_type_def, compile_assign_value_def,
       is_bytestring_type_def, pop_global_body_struct_bytes,
       comp_bind_def, comp_return_def,
       comp_ignore_bind_def] >>
  gen_tac >> Cases_on `compile_alloc_buffer 128 x` >> simp[] >>
  rename1 `compile_storage_to_memory (Lit 4w) buf.buf_operand 4 st` >>
  Cases_on `compile_storage_to_memory (Lit 4w) buf.buf_operand 4 st` >> simp[]
QED

Theorem pop_global_return_boundary:
  compile_stmt pop_global_body_env NoLoop (BaseT (UintT 256))
    (Return (SOME (Literal (BaseT (UintT 256)) (IntL 0)))) =
  emit_inst RET [Lit 0w; Var "%5"] []
Proof
  simp[Once compile_stmt_def, pop_global_body_return_pc,
       compile_internal_return_from_env_def, pop_global_body_return_buf,
       pop_global_body_return_count, compile_internal_return_def] >>
  simp[lower_value_def, FUN_EQ_THM, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, Once compile_expr_def, expr_type_def,
       compile_literal_vv_def, unwrap_value_def] >>
  EVAL_TAC >> simp[]
QED

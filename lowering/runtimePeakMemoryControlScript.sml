(* Branch and loop construction preserves each block's allocation windows. *)
Theory runtimePeakMemoryControl
Ancestors
  runtimePeakMemoryCode runtimePeakMemoryExpr stmtLowering compileEnv
  context emitHelper venomInst vyperAST finite_map list

fun windows_tac thms =
  rpt (FIRST [
    CHANGED_TAC (simp(thms @ [LET_THM, pairTheory.FORALL_PROD, pairTheory.UNCURRY_DEF,
      dalloca_windows_emit_helpers, dalloca_windows_new_block,
      dalloca_windows_fresh, dalloca_windows_return, dalloca_windows_select,
      dalloca_windows_alloc_buffer, dalloca_windows_ptr_access,
      dalloca_windows_lower_value])),
    gen_tac, irule dalloca_windows_bind >> conj_tac,
    irule dalloca_windows_ignore_bind >> conj_tac,
    COND_CASES_TAC, BasicProvers.TOP_CASE_TAC]);

Theorem dalloca_windows_get:
  preserves_dalloca_windows window comp_get
Proof
  simp[preserves_dalloca_windows_def, comp_get_def]
QED

Theorem dalloca_windows_jmp_if_live:
  preserves_dalloca_windows window (emit_jmp_if_not_terminated label)
Proof
  simp[emit_jmp_if_not_terminated_def] >> windows_tac [dalloca_windows_get]
QED

Theorem dalloca_windows_declare_local:
  preserves_dalloca_windows window (declare_local cenv id ty)
Proof
  simp[declare_local_def] >> windows_tac []
QED

Theorem dalloca_windows_emit_local_alloca:
  preserves_dalloca_windows window (emit_local_alloca cenv id)
Proof
  simp[emit_local_alloca_def] >> windows_tac []
QED

Theorem dalloca_windows_stmt_if:
  preserves_dalloca_windows window (compile_expr cenv (BaseT BoolT) cond) /\
  preserves_dalloca_windows window (compile_stmts cenv lctx ty then_ss) /\
  preserves_dalloca_windows window (compile_stmts cenv lctx ty else_ss) ==>
  preserves_dalloca_windows window (compile_stmt cenv lctx ty (If cond then_ss else_ss))
Proof
  strip_tac >> simp[Once compile_stmt_def] >>
  windows_tac [dalloca_windows_get, dalloca_windows_jmp_if_live]
QED

Theorem dalloca_windows_range_checks:
  preserves_dalloca_windows window (compile_range_bound_checks s e n bound signed)
Proof
  simp[compile_range_bound_checks_def] >> windows_tac []
QED

Theorem dalloca_windows_stmt_range:
  preserves_dalloca_windows window (compile_expr cenv fty start_e) /\
  preserves_dalloca_windows window (compile_expr cenv fty end_e) /\
  (!ce lc. preserves_dalloca_windows window (compile_stmts ce lc ty stmts)) ==>
  preserves_dalloca_windows window
    (compile_stmt cenv lctx ty (For id fty (Range start_e end_e) bound stmts))
Proof
  strip_tac >> simp[Once compile_stmt_def] >>
  windows_tac [dalloca_windows_declare_local, dalloca_windows_emit_local_alloca,
               dalloca_windows_range_checks, dalloca_windows_jmp_if_live]
QED

Theorem dalloca_windows_declare_stmt_local:
  preserves_dalloca_windows window (declare_stmt_local cenv stmt)
Proof
  Cases_on `stmt` >>
  simp[declare_stmt_local_def, dalloca_windows_declare_local, dalloca_windows_return]
QED

Theorem dalloca_windows_stmt_list_cons:
  (!ce. preserves_dalloca_windows window (compile_stmt ce lctx ty stmt)) /\
  (!ce. preserves_dalloca_windows window (compile_stmts ce lctx ty rest)) ==>
  preserves_dalloca_windows window (compile_stmts cenv lctx ty (stmt::rest))
Proof
  strip_tac >> simp[Once compile_stmt_def] >>
  windows_tac [dalloca_windows_get, dalloca_windows_declare_stmt_local]
QED

Theorem dalloca_windows_iter_elem_copy:
  preserves_dalloca_windows window
    (compile_iter_elem_copy cenv src dst n loc slots dst_ty src_ty)
Proof
  simp[compile_iter_elem_copy_def, compile_slot_to_memory_def,
       compile_word_copy_loop_def, compile_word_copy_loop_op_def,
       compile_word_copy_loop_base_def] >>
  windows_tac [dalloca_windows_imm_copy, dalloca_windows_copy_memory,
               dalloca_windows_store_memory]
QED

Theorem dalloca_windows_stmt_array:
  preserves_dalloca_windows window (compile_expr cenv (expr_type arr) arr) /\
  (!ce lc. preserves_dalloca_windows window (compile_stmts ce lc ty stmts)) ==>
  preserves_dalloca_windows window
    (compile_stmt cenv lctx ty (For id fty (Array arr) bound stmts))
Proof
  strip_tac >> simp[Once compile_stmt_def] >>
  windows_tac [dalloca_windows_declare_local, dalloca_windows_emit_local_alloca,
               dalloca_windows_iter_elem_copy, dalloca_windows_jmp_if_live]
QED

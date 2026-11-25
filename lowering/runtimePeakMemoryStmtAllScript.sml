(* Statements use unrestricted expression preservation for conditions,
   assignment places and declaration initializers. *)
Theory runtimePeakMemoryStmtAll
Ancestors
  runtimePeakMemoryExprAll runtimePeakMemoryStmt runtimePeakMemoryControl
  runtimePeakMemoryStmtOps runtimePeakMemoryExpr runtimePeakMemoryBuiltins
  runtimePeakMemoryCode runtimePeakMemoryAbi
  entryStatementStoreCode stmtLowering exprLowering compileEnv context
  emitHelper venomInst vyperAST list pair fragFuel

(* Split sequencing, then discharge the individual compiler operations. *)
val stmt_windows_tac =
  rpt (FIRST [
    gen_tac,
    irule dalloca_windows_bind >> conj_tac,
    irule dalloca_windows_ignore_bind >> conj_tac,
    CHANGED_TAC (simp[LET_THM, pairTheory.UNCURRY_DEF, comp_bind_return,
      dalloca_windows_emit_helpers, dalloca_windows_new_block,
      dalloca_windows_fresh, dalloca_windows_return, dalloca_windows_select,
      dalloca_windows_alloc_buffer, dalloca_windows_ptr_access,
      dalloca_windows_unwrap_value, dalloca_windows_lower_value,
      dalloca_windows_get, dalloca_windows_jmp_if_live,
      dalloca_windows_declare_local, dalloca_windows_declare_stmt_local,
      dalloca_windows_range_checks, dalloca_windows_iter_elem_copy,
      dalloca_windows_emit_local_alloca, dalloca_windows_store_at_loc,
      dalloca_windows_assign_value, dalloca_windows_snapshot,
      dalloca_windows_binop, dalloca_windows_revert_with_reason,
      dalloca_windows_internal_return_from_env, dalloca_windows_return_unlock,
      dalloca_windows_external_return, dalloca_windows_nonreentrant,
      dalloca_windows_store_memory_typed, dalloca_windows_store_memory,
      dalloca_windows_dynarray_append, dalloca_windows_abi_encode,
      dalloca_windows_log_saved_topics, dalloca_windows_abi_encode_values]),
    irule dalloca_windows_revert_with_custom_error,
    irule dalloca_windows_ext_call_args,
    irule dalloca_windows_tuple_unpack,
    irule dalloca_windows_reason_message,
    CHANGED_TAC (first_assum irule >> simp[]),
    COND_CASES_TAC, BasicProvers.TOP_CASE_TAC, pairarg_tac]);

Theorem dalloca_windows_compile_stmts_all:
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) /\
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) /\
  (!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
  ((!ce lc ty s. preserves_dalloca_windows window (compile_stmt ce lc ty s)) /\
   (!ce lc ty ss. preserves_dalloca_windows window (compile_stmts ce lc ty ss)))
Proof
  strip_tac >>
  `!ce ty e. preserves_dalloca_windows window (compile_expr ce ty e)` by
    (rw[dalloca_windows_result_state] >>
     mp_tac dalloca_windows_compile_expr_all_mutual >>
     (impl_tac >- simp[]) >> strip_tac >> first_assum irule >> simp[]) >>
  `!ce bt. preserves_dalloca_windows window
             (compile_get_target_ptr compile_expr ce bt)` by
    (rpt gen_tac >> irule dalloca_windows_get_target_ptr >> simp[]) >>
  ho_match_mp_tac compile_stmt_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
  simp[Once compile_stmt_def, LET_THM, pairTheory.UNCURRY_DEF, comp_bind_return]
  (* Work backwards in small batches, treating the two loop cases separately. *)
  >>> SPLIT_LT 23 (ALL_LT, ALLGOALS stmt_windows_tac)
  >>> SPLIT_LT 22 (ALL_LT, ALLGOALS stmt_windows_tac)
  >>> SPLIT_LT 21 (ALL_LT, ALLGOALS stmt_windows_tac)
  >>> SPLIT_LT 17 (ALL_LT, SPLIT_LT 4 (ALLGOALS stmt_windows_tac, ALL_LT))
  >>> SPLIT_LT 12 (ALL_LT, SPLIT_LT 5 (ALLGOALS stmt_windows_tac, ALL_LT))
  >>> SPLIT_LT 7 (ALL_LT, SPLIT_LT 5 (ALLGOALS stmt_windows_tac, ALL_LT))
  >>> SPLIT_LT 3 (ALL_LT, SPLIT_LT 4 (ALLGOALS stmt_windows_tac, ALL_LT))
  >>> SPLIT_LT 3 (ALLGOALS stmt_windows_tac, ALL_LT) >>
  (* The live state supplies the witness required by the list IHs. *)
  HINT_EXISTS_TAC >> simp[]
QED

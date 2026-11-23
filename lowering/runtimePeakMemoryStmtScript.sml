(* Window preservation follows statement recursion and declaration scope. *)
Theory runtimePeakMemoryStmt
Ancestors
  runtimePeakMemoryControl runtimePeakMemoryExprDispatch runtimePeakMemoryExpr
  runtimePeakMemoryStmtOps runtimePeakMemoryBuiltins runtimePeakMemoryArity runtimePeakMemorySourceGate
  runtimePeakMemoryCode runtimePeakMemoryAbi
  entryStatementStoreCode stmtLowering exprLowering supportedStmtTraverse
  supportedExprTraverse compileEnv context emitHelper venomInst vyperAST list fragFuel

Theorem dalloca_windows_bind_declare_local:
  (!ce'. ce'.ce_func_defaults = ce.ce_func_defaults ==>
     preserves_dalloca_windows window (f ce')) ==>
  preserves_dalloca_windows window (comp_bind (declare_local ce id ty) f)
Proof
  strip_tac >> match_mp_tac (Q.ISPEC `\ce'. ce'.ce_func_defaults = ce.ce_func_defaults`
    (Q.GEN `P` dalloca_windows_bind_result)) >>
  simp[dalloca_windows_declare_local, declare_local_defaults]
QED

Theorem dalloca_windows_bind_declare_stmt_local:
  (!ce'. ce'.ce_func_defaults = ce.ce_func_defaults ==>
     preserves_dalloca_windows window (f ce')) ==>
  preserves_dalloca_windows window (comp_bind (declare_stmt_local ce s) f)
Proof
  strip_tac >> match_mp_tac (Q.ISPEC `\ce'. ce'.ce_func_defaults = ce.ce_func_defaults`
    (Q.GEN `P` dalloca_windows_bind_result)) >>
  simp[dalloca_windows_declare_stmt_local, declare_stmt_local_defaults]
QED

fun windows_tac thms =
  rpt (FIRST [
    CHANGED_TAC (simp(thms @ [LET_THM, pairTheory.FORALL_PROD, pairTheory.UNCURRY_DEF,
      dalloca_windows_emit_helpers, dalloca_windows_new_block,
      dalloca_windows_fresh, dalloca_windows_return, dalloca_windows_select,
      dalloca_windows_alloc_buffer, dalloca_windows_ptr_access, dalloca_windows_unwrap_value,
      dalloca_windows_lower_value, dalloca_windows_get, dalloca_windows_jmp_if_live,
      comp_bind_return])),
    gen_tac,
    irule dalloca_windows_bind_declare_local >> rpt strip_tac,
    irule dalloca_windows_bind_declare_stmt_local >> rpt strip_tac,
    irule dalloca_windows_bind >> conj_tac,
    irule dalloca_windows_ignore_bind >> conj_tac,
    COND_CASES_TAC, BasicProvers.TOP_CASE_TAC, pairarg_tac]);

Theorem dalloca_windows_compile_place:
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) /\
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) /\
  (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        compile_env_blueprint_free ce) /\ compile_env_builtin_arity ce /\
  (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        ~supported_target_exists blueprint_create_root bt) /\
  ~supported_target_exists short_builtin_args bt ==>
  preserves_dalloca_windows window (compile_get_target_ptr compile_expr ce bt)
Proof
  strip_tac >> irule dalloca_windows_get_target_ptr >>
  rpt strip_tac >> irule dalloca_windows_compile_expr >> simp[] >>
  metis_tac[supported_target_contains_expr]
QED

Theorem dalloca_windows_supported_tuple_member[local]:
  !ts.
  MEM (BaseTarget bt) ts /\ ~supported_assignments_exists root ts ==>
  ~supported_target_exists root bt
Proof
  Induct >> simp[supported_assignment_exists_def] >> metis_tac[supported_assignment_exists_def]
QED

val compile_stmt_windows_tac =
  rpt (FIRST [
    CHANGED_TAC (windows_tac [dalloca_windows_range_checks, dalloca_windows_iter_elem_copy,
      dalloca_windows_emit_local_alloca, dalloca_windows_store_at_loc,
      dalloca_windows_assign_value, dalloca_windows_snapshot, dalloca_windows_tuple_unpack,
      dalloca_windows_binop, dalloca_windows_reason_message,
      dalloca_windows_revert_with_reason, dalloca_windows_revert_with_custom_error,
      dalloca_windows_internal_return_from_env, dalloca_windows_return_unlock,
      dalloca_windows_external_return, dalloca_windows_nonreentrant,
      dalloca_windows_store_memory_typed, dalloca_windows_store_memory,
      dalloca_windows_dynarray_append, dalloca_windows_abi_encode,
      dalloca_windows_log_saved_topics, dalloca_windows_abi_encode_values]),
    CHANGED_TAC strip_tac,
    (fs[compile_env_blueprint_free_def, compile_env_builtin_arity_def] >> NO_TAC),
    CHANGED_TAC (first_assum irule >> simp[]),
    irule dalloca_windows_revert_with_custom_error,
    irule dalloca_windows_ext_call_args,
    irule dalloca_windows_tuple_unpack,
    irule dalloca_windows_reason_message,
    irule dalloca_windows_lower_value,
    irule dalloca_windows_compile_expr >> simp[],
    irule dalloca_windows_compile_place >> simp[]]);

Theorem dalloca_windows_compile_stmt_mutual[local]:
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) /\
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) ==>
  ((!ce lc ty s.
    (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        compile_env_blueprint_free ce) /\ compile_env_builtin_arity ce /\
    (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        ~supported_stmt_expr_exists blueprint_create_root s) /\
    ~supported_stmt_expr_exists short_builtin_args s ==>
    preserves_dalloca_windows window (compile_stmt ce lc ty s)) /\
   (!ce lc ty ss.
    (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        compile_env_blueprint_free ce) /\ compile_env_builtin_arity ce /\
    (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        ~supported_stmts_expr_exists blueprint_create_root ss) /\
    ~supported_stmts_expr_exists short_builtin_args ss ==>
    preserves_dalloca_windows window (compile_stmts ce lc ty ss)))
Proof
  strip_tac >> ho_match_mp_tac compile_stmt_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
  gvs[supported_stmt_expr_exists_def, supported_assignment_exists_def,
      supported_assert_exists_def, supported_raise_exists_def, supported_iterator_exists_def,
      supported_expr_exists_def, supported_exprs_exists_every, EXISTS_MEM] >>
  simp[Once compile_stmt_def]
  (* Run the 27 induction cases in smaller groups, starting at the end
     so the earlier goal positions stay fixed. *)
  >>> SPLIT_LT 23 (ALL_LT, ALLGOALS compile_stmt_windows_tac)
  >>> SPLIT_LT 18 (ALL_LT, SPLIT_LT 5 (ALLGOALS compile_stmt_windows_tac, ALL_LT))
  >>> SPLIT_LT 9 (ALL_LT, SPLIT_LT 9 (ALLGOALS compile_stmt_windows_tac, ALL_LT))
  >>> SPLIT_LT 9 (ALLGOALS compile_stmt_windows_tac, ALL_LT) >>
  FIRST [
    (* Member exclusions for custom errors, logs and tuple assignment. *)
    qpat_assum `MEM _ _` (K ALL_TAC) >>
    metis_tac[dalloca_windows_supported_tuple_member],
    (* Instantiate the list induction hypotheses at the live block. *)
    qpat_assum `~block_is_terminated _` (K ALL_TAC) >> metis_tac[],
    (* Declaration scope preserves the function defaults. *)
    `compile_env_blueprint_free ce` by metis_tac[] >>
    fs[compile_env_blueprint_free_def]]
QED

Theorem dalloca_windows_compile_stmts:
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) /\
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) /\
  (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        compile_env_blueprint_free ce) /\ compile_env_builtin_arity ce /\
  (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        ~supported_stmts_expr_exists blueprint_create_root ss) /\
  ~supported_stmts_expr_exists short_builtin_args ss ==>
  preserves_dalloca_windows window (compile_stmts ce lc ty ss)
Proof
  metis_tac[dalloca_windows_compile_stmt_mutual]
QED

Theory vyperSubscriptOverlapCV
Ancestors
  list alist vyperAST vyperTypeCallGraph
  vyperSubscriptOverlap
Libs
  cv_transLib

val () = cv_auto_trans risky_builtin_def;

val () = cv_auto_trans risky_call_target_def;

val () = cv_auto_trans accesses_expr_def;

val () = cv_auto_trans accesses_atarget_def;

val () = cv_auto_trans accesses_iterator_def;

val () = cv_auto_trans accesses_assert_reason_def;

val () = cv_auto_trans accesses_raise_reason_def;

val () = cv_auto_trans accesses_stmt_def;

val () = cv_auto_trans find_function_def;

val () = cv_auto_trans callee_accesses_def;

val () = cv_auto_trans function_accesses_def;

val () = cv_auto_trans int_calls_expr_def;

val () = cv_auto_trans int_calls_atarget_def;

val () = cv_auto_trans int_calls_iterator_def;

val () = cv_auto_trans int_calls_assert_reason_def;

val () = cv_auto_trans int_calls_raise_reason_def;

val () = cv_auto_trans int_calls_stmt_def;

val () = cv_auto_trans function_int_calls_def;

val () = cv_auto_trans toplevel_call_edges_def;

val () = cv_auto_trans module_call_edges_def;

val () = cv_auto_trans contract_call_edges_def;

val () = cv_auto_trans contract_call_nodes_def;

val () = cv_auto_trans direct_callees_def;

val () = cv_auto_trans reachable_nodes_def;

val () = cv_auto_trans reached_functions_def;

val () = cv_auto_trans expr_accesses_def;

val () = cv_auto_trans constant_decl_def;

val nonconstant_reads_pre_def =
  cv_auto_trans_pre "nonconstant_reads_pre" nonconstant_reads_def;

Theorem nonconstant_reads_pre[cv_pre]:
  ∀mods accs. nonconstant_reads_pre mods accs
Proof
  ho_match_mp_tac nonconstant_reads_ind \\ rw[]
  \\ rw[Once nonconstant_reads_pre_def]
  \\ gvs[]
QED

val () = cv_auto_trans any_written_def;

val () = cv_auto_trans subscript_overlap_def;

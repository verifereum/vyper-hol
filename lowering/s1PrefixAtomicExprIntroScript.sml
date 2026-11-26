(* Request-prefix introductions for atomic expressions. *)
Theory s1PrefixAtomicExprIntro
Ancestors
  s1PrefixPreds s1PrefixNames s1PrefixLiteralWord s1PrefixFrame s1PrefixDefs
  vyperAST vyperInterpreter vyperStorageTrace vyperState
Libs
  pairLib

Theorem atomic_expr_prefix_ok:
  !cx e.
    ((?a id. e = Name a id) \/ (?a nsid. e = TopLevelName a nsid) \/
     (?a nsid mid. e = FlagMember a nsid mid) \/ (?a l. e = Literal a l)) ==>
    body_expr_prefix_ok cx e
Proof
  rpt strip_tac >> gvs[body_expr_prefix_ok_def, name_value_prefix, name_vv_prefix,
                       toplevel_name_value_prefix, toplevel_name_vv_prefix,
                       literal_word_value_prefix, literal_vv_prefix] >>
  rw[expr_sim_prefix_def, expr_vv_sim_prefix_def,
     expr_sim_full_pre_def, expr_vv_sim_full_pre_def] >>
  irule gas_prefix_full_no_outcome >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, Once evaluate_def] >>
  PairCases_on `nsid` >>
  simp[lookup_flag_mem_def] >> rpt gen_tac >> rpt BasicProvers.TOP_CASE_TAC >>
  simp[bind_def, read_result_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[]
QED

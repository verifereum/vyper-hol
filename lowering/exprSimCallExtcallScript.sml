(*
 * The piece of exprSimCalls's compile_extcall_sim: extcall/staticcall in SOME oracle mode, reverts and default_return_value (#553).
 * extcall_expr_vv_ok is compile_extcall_sim's statement; exprSimCalls takes it as is.
 *)

Theory exprSimCallExtcall
Ancestors
  list rich_list exprSimHyps exprSimExtCallCase vyperAST

Theorem extcall_expr_vv_ok:
  !cenv ann is_static skip sig opts args dflt.
    expr_sim_below cenv (expr_size (Call ann (ExtCall is_static skip sig opts) args dflt)) ==>
    expr_vv_ok cenv (Call ann (ExtCall is_static skip sig opts) args dflt)
Proof
  rpt strip_tac >> simp[expr_vv_ok_case] >> rpt gen_tac >>
  `EVERY (expr_ok cenv) args` by
    (simp[EVERY_MEM] >> rpt strip_tac >> irule expr_sim_below_mem >>
     qexists_tac `args` >> simp[] >> irule expr_sim_below_mono >>
     goal_assum (drule_at Any) >> simp[expr_size_def]) >>
  irule (cj 2 (SPEC_ALL compile_extcall_case)) >> rpt conj_tac >>
  rpt strip_tac >>
  FIRST [irule exprs_case_every_ok, irule results_case_every_ok] >>
  fs[EVERY_MEM] >> metis_tac[MEM_TAKE, MEM_DROP_IMP]
QED

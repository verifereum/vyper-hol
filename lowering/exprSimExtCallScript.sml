(*
 * Expression simulation: extcall and staticcall (#636, Calls row 1)
 *
 * extcall/staticcall in oracle mode, including reverts and
 * default_return_value (#553).  The source evaluates the target, then the
 * positional arguments without reading them (eval_expr_results), then the
 * keyword operands, and reads the arguments last; the hypotheses of
 * compile_extcall_case give the operands' judgments in that order, as the
 * body induction's hypotheses do (bodySimExprCases' body_extcall_case).
 *
 * TOP-LEVEL:
 *   compile_extcall_case — extcall's expr_sim_case and expr_vv_case from
 *     its operands' judgments, for compile_expr_sim and the body
 *     simulation; compile_extcall_case_sim, expr_vv_ok of extcall, follows
 *
 * compile_extcall_case is cheated: as defined it is false for dynamic
 * arguments, whose calldata the lowering sends at the argument tuple's ABI
 * size bound (as Python at VYPER_PIN does) while the source sends the exact
 * encoding (build_ext_calldata).
 *)

Theory exprSimExtCall
Ancestors
  list rich_list exprSim exprSimHyps vyperAST vyperInterpreter

Theorem compile_extcall_case:
  !nocalls ctx func cenv cx ann is_static skip sig opts args dflt.
    exprs_case nocalls ctx func cenv cx (TAKE 1 args) /\
    (!s target t.
       eval_exprs cx (TAKE 1 args) s = (INL target, t) ==>
       results_case nocalls ctx func cenv cx
         (TAKE (LENGTH (FST (SND sig))) (DROP 1 args))) /\
    (!s target t s' results t'.
       eval_exprs cx (TAKE 1 args) s = (INL target, t) /\
       eval_expr_results cx (TAKE (LENGTH (FST (SND sig))) (DROP 1 args)) s' =
         (INL results, t') ==>
       exprs_case nocalls ctx func cenv cx
         (DROP (1 + LENGTH (FST (SND sig))) args)) ==>
    expr_sim_case nocalls ctx func cenv cx
      (Call ann (ExtCall is_static skip sig opts) args dflt) /\
    expr_vv_case nocalls ctx func cenv cx
      (Call ann (ExtCall is_static skip sig opts) args dflt)
Proof
  cheat
QED

Theorem compile_extcall_case_sim:
  !cenv ann is_static skip sig opts args dflt.
    expr_sim_below cenv
      (expr_size (Call ann (ExtCall is_static skip sig opts) args dflt)) ==>
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

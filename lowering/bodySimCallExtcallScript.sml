(* Piece of bodySimCallCases.body_extcall_case. *)

Theory bodySimCallExtcall
Ancestors
  bodySimExprCases exprSimExtCallCase
  list bodySim exprSimHyps exprSimHypsDefs vyperAST vyperInterpreter vyperState
  vyperContext vyperTypeCallGraph

Theorem body_results_ok_case[local]:
  !cx es tops ctx func cenv.
    body_results_ok cx es /\ body_inv tops ctx cenv cx ==>
    results_case F ctx func cenv cx es
Proof
  gen_tac >> Induct >> rw[body_results_ok_def, results_case_def] >>
  metis_tac[body_expr_ok_case]
QED

(* exprSimExtCallCase's compile_extcall_case, from the operands' judgments
   in the order the source evaluates them. *)
Theorem extcall_body_expr_ok:
  !cx v14 is_static skip_check sig opts es v15.
    (!s'' target t nargs s'3' results t'.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) /\
       eval_expr_results cx (TAKE nargs (DROP 1 es)) s'3' = (INL results,t') ==>
       body_exprs_ok cx (DROP (1 + nargs) es)) /\
    (!s'' target t nargs.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) ==>
       body_results_ok cx (TAKE nargs (DROP 1 es))) /\
    body_exprs_ok cx (TAKE 1 es) ==>
    body_expr_ok cx (Call v14 (ExtCall is_static skip_check sig opts) es v15)
Proof
  rpt strip_tac >> irule body_expr_ok_of_case >> conj_tac >- gvs[] >> simp[] >> rpt gen_tac >> strip_tac >>
  irule compile_extcall_case >> rpt conj_tac >> rpt strip_tac
  >- metis_tac[body_exprs_ok_case]
  >- metis_tac[body_results_ok_case] >>
  metis_tac[body_exprs_ok_case]
QED

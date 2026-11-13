(* Piece of bodySimCallCases.body_extcall_case. *)

Theory bodySimCallExtcall
Ancestors
  bodySimExprCases exprSimExtCallCase
  list bodySim exprSimHyps exprSimHypsDefs vyperAST vyperInterpreter vyperState
  vyperContext vyperTypeCallGraph

(* exprSimExtCallCase's compile_extcall_case, from the operands' judgments
   in the order the source evaluates them. *)
Theorem extcall_body_expr_ok:
  !cx v14 is_static skip_check sig opts es v15.
    (!s'' target t nargs s'3' vs t'.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) /\
       eval_exprs cx (TAKE nargs (DROP 1 es)) s'3' = (INL vs,t') ==>
       body_exprs_ok cx (DROP (1 + nargs) es)) /\
    (!s'' target t nargs.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) ==>
       body_exprs_ok cx (TAKE nargs (DROP 1 es))) /\
    body_exprs_ok cx (TAKE 1 es) ==>
    !tops ctx func cenv.
      body_inv tops ctx cenv cx ==>
      expr_sim_case F ctx func cenv cx (Call v14 (ExtCall is_static skip_check sig opts) es v15) /\
      expr_vv_case F ctx func cenv cx (Call v14 (ExtCall is_static skip_check sig opts) es v15)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  irule compile_extcall_case >> rpt conj_tac >> rpt strip_tac
  >> metis_tac[body_exprs_ok_case]
QED

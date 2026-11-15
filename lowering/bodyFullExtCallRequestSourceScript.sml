(* Source bridges for immediate-read external-call operands. *)
Theory bodyFullExtCallRequestSource
Ancestors
  bodyFullPreds vyperInterpreter vyperState bodyIntCallJointPureSource
  bodyFullExtCallRequestInterfaces supportedExprTraverse vyperAST
  vyperStatePreservation vyperPlaceFrames vyperContext vyperMisc
  list pair sum exprCallBounds exprCallbackContracts

Theorem body_results_full_ok_imp_exprs_full_ok:
  !cx xs. body_results_full_ok cx xs ==> body_exprs_full_ok cx xs
Proof
  gen_tac >> Induct_on `xs` >>
  simp[body_results_full_ok_def, body_exprs_full_ok_def] >>
  metis_tac[]
QED

Theorem eval_exprs_success_results:
  !xs cx s vs t. eval_exprs cx xs s = (INL vs,t) ==>
    ?rs. eval_expr_results cx xs s = (INL rs,t)
Proof
  Induct_on `xs`
  >- simp[evaluate_def, return_def] >>
  rpt gen_tac >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx h s` >> Cases_on `q` >>
  simp[] >>
  Cases_on `read_result cx x r` >> Cases_on `q` >>
  simp[] >>
  drule read_result_state >> strip_tac >> gvs[] >>
  Cases_on `eval_exprs cx xs r` >> Cases_on `q` >>
  simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  simp[Once evaluate_def, bind_def, return_def] >>
  metis_tac[]
QED


Theorem extcall_request_tail_frame:
  !cenv cx env ann stat skip name ats rt opts args dr es st res st'.
    expr_body_pre cenv cx env
      (Call ann (ExtCall stat skip (name,ats,rt) opts) args dr) es /\
    eval_exprs cx (DROP 1 args) st = (res,st') ==>
    (st' with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) =
    (st with <|gas_obs := []; outcomes := NONE; storage_trace := []|>)
Proof
  rpt strip_tac >>
  drule extcall_request_tail_effect_free >> strip_tac >>
  drule_all effect_free_eval_exprs_frame >> simp[]
QED

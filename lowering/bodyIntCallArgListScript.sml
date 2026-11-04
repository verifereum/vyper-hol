(* Reachability-guarded source eligibility for deferred internal arguments. *)
Theory bodyIntCallArgList
Ancestors
  list bodySim bodyIntCallArgLifetime exprLoweringProps vyperInterpreter vyperState

Theorem body_results_head_vv_sim:
  body_inv tops ctx cenv cx /\ body_results_ok cx (e::rest) /\
  expr_body_pre cenv cx env e ss ==>
  expr_vv_sim ctx func cenv cx (expr_type e) e ss
Proof
  simp[body_results_ok_def, body_expr_ok_def] >> metis_tac[]
QED

Theorem body_results_success_tail:
  body_results_ok cx (e::rest) /\
  eval_expr cx e ss = (INL raw,ss') ==>
  body_results_ok cx rest
Proof
  simp[body_results_ok_def] >> metis_tac[]
QED

Theorem pure_argument_tail_pre:
  supported_pure_expr tops e /\ eval_expr cx e ss = (res,ss') /\
  EVERY (\a. expr_body_pre cenv cx env a ss) rest ==>
  EVERY (\a. expr_body_pre cenv cx env a ss') rest
Proof
  metis_tac[supported_pure_eval_expr_state]
QED

Theorem compile_expr_local_ptrs_reserved:
  local_ptrs_reserved cenv sa /\
  compile_expr cenv ty e sa = (vv,sb) ==>
  local_ptrs_reserved cenv sb
Proof
  metis_tac[cj 1 compile_expr_grows, local_ptrs_reserved_next_var]
QED

Theorem supported_pure_eval_expr_results_state:
  EVERY (supported_pure_expr tops) args /\
  eval_expr_results cx args ss = (res,ss') ==> ss' = ss
Proof
  map_every qid_spec_tac [`ss`, `res`, `ss'`] >> Induct_on `args` >>
  simp[Once evaluate_def, return_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[bind_def, return_def, AllCaseEqs()] >>
  metis_tac[supported_pure_eval_expr_state]
QED

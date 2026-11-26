Theory boolChainWrapperRead
Ancestors
  boolChainSource vyperInterpreter vyperState

(* Observing the wrapper's result reads back the value it already forced. *)
Theorem bool_chain_wrapper_read_action:
  expr_body_pre cenv cx env (Builtin ann (BoolChain d n) [e]) es ==>
  !gs. bind (eval_expr cx (Builtin ann (BoolChain d n) [e])) (read_result cx)
          (es with gas_obs := gs) =
       bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs)
Proof
  strip_tac >> drule_then strip_assume_tac bool_chain_wrapper_action >>
  gen_tac >> simp[Once bind_def] >>
  Cases_on `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs)` >>
  rename1 `bind (eval_expr cx e) _ _ = (res,ee)` >> Cases_on `res` >>
  gvs[bind_def, return_def, read_result_def]
QED

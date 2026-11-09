Theory bodyPtrIfExpRawConditional
Ancestors
  bodyPtrIfExpWordMarked bodyPtrIfExpConditionalSource
  gasSummaryComposePtr fragGasPathPtr exprSimUnwrapProps exprSimDefs
  vyperState loweringPosts exprSimSource exprSimUnwrap fragGasSeqPtr

(* Source transport does not depend on the target representation or unwrap
   equation. A no-op unwrap can use this directly, with no extra path. *)
Theorem ifexp_raw_marked_conditional:
  gas_marked_exec_ptr D (ctx,fn) PG (eval_expr cx e) (es,s0,G0,tn0)
    marks (INL raw) ee G tn (OK s) /\
  vv_post ctx fn ce cx e es sa sb s0 (ee with gas_obs := []) raw vv s /\
  gas_admissible (bind (eval_expr cx e) (conditional_result cx)) expr_vv_res_ok es ==>
  ?tv v.
    gas_marked_exec_ptr D (ctx,fn) PG
      (bind (eval_expr cx e) (conditional_result cx)) (es,s0,G0,tn0)
      marks (INL tv) ee G tn (OK s) /\
    read_result cx raw (ee with gas_obs := []) = (INL v,ee with gas_obs := []) /\
    read_result cx tv (ee with gas_obs := []) = (INL v,ee with gas_obs := [])
Proof
  strip_tac >>
  `?v. read_result cx raw (ee with gas_obs := []) =
       (INL v,ee with gas_obs := [])` by
    (Cases_on `read_result cx raw (ee with gas_obs := [])` >>
     rename1 `_ = (res,st)` >>
     `st = ee with gas_obs := []` by metis_tac[read_result_state] >> gvs[] >>
     Cases_on `res` >> metis_tac[vv_post_failed_read]) >>
  drule_all ifexp_marked_conditional_source >> strip_tac >>
  qexistsl_tac [`tv`, `v`] >> simp[] >>
  irule ifexp_raw_marked_word_then >> simp[] >>
  qexistsl_tac [`G`, `raw`, `s`, `tn`] >> simp[] >>
  irule (cj 1 gas_path_ptr_rules) >>
  metis_tac[gas_path_ptr_ok_not_halted, gas_marked_exec_ptr_def]
QED

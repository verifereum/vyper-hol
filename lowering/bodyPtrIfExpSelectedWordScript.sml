Theory bodyPtrIfExpSelectedWord
Ancestors
  bodyPtrIfExpWordMarked bodyPtrIfExpWord

Theorem ifexp_selected_word_marked:
  expr_body_pre cenv cx env e es /\ is_word_type (expr_type e) /\
  compile_expr cenv ty e sa = (vv,sm) /\ unwrap_value cenv vv sm = (op,sb) /\
  gas_marked_exec_ptr D (ctx,fn) PG (eval_expr cx e) (es,s0,G0,tn0)
    marks (INL raw) ee G tn (OK s) /\
  gas_admissible (bind (eval_expr cx e) (conditional_result cx)) expr_vv_res_ok es /\
  vv_post ctx fn cenv cx e es sa sm s0 (ee with gas_obs := []) raw vv s /\
  ptr_vv_ok cx (expr_type e) raw vv (ee with gas_obs := []) G tn s /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v tv u G1 tn1.
    gas_marked_exec_ptr D (ctx,fn) PG
      (bind (eval_expr cx e) (conditional_result cx)) (es,s0,G0,tn0)
      marks (INL tv) ee G1 tn1 (OK u) /\
    read_result cx tv (ee with gas_obs := []) = (INL v,ee with gas_obs := []) /\
    expr_post ctx fn cenv cx e es sa sb s0 (ee with gas_obs := []) v op u /\
    ptr_val_ok cx (expr_type e) v op G1 tn1 u /\
    ghost_inv d cenv cx (ee with gas_obs := []) G1 tn1 u /\
    ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all ifexp_raw_marked_word_unwrap >> strip_tac >>
  drule_all ifexp_marked_conditional_source >> strip_tac >>
  drule_all ifexp_raw_marked_word_then >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

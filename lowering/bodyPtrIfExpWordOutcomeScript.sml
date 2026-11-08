Theory bodyPtrIfExpWordOutcome
Ancestors
  bodyPtrIfExpSelectedWord bodyPtrDefs gasSummaryComposePtr fragGasPathPtr
  bodyPtrIfExpWordMarked
  bodyPtrIfExpSource vyperInterpreter vyperState exprSimDefs gasContext

Theorem ifexp_arm_raw_admissible[local]:
  gas_admissible (bind (eval_expr cx e) (conditional_result cx))
    expr_vv_res_ok es ==>
  gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  simp[gas_admissible_def] >> rpt strip_tac >>
  Cases_on `res` >> gvs[expr_vv_res_ok_def]
  >- (rename1 `eval_expr cx e _ = (INL raw,ee)` >>
      Cases_on `raw` >> simp[] >>
      first_x_assum (qspec_then `gs` mp_tac) >>
      simp[bind_def, conditional_result_def, raise_def, expr_vv_res_ok_def]) >>
  first_x_assum (qspec_then `gs` mp_tac) >>
  simp[bind_def, expr_vv_res_ok_def]
QED

Theorem ifexp_selected_word_outcome_ptr:
  expr_vv_sim_ptr d ctx PG fn cenv cx ty e es /\
  expr_body_pre cenv cx env e es /\ is_word_type (expr_type e) /\
  compile_expr cenv ty e sa = (vv,sm) /\ unwrap_value cenv vv sm = (op,sb) /\
  fn_has_code sa sm fn /\ fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (conditional_result cx)) expr_vv_res_ok es /\
  stmt_state_rel ctx fn cenv cx es s0 /\ ghost_inv d cenv cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
    (bind (eval_expr cx e) (conditional_result cx)) (es,s0,G0,tn0)
    (\res ee G tn u. ?tv v. res = INL tv /\
       read_result cx tv ee = (INL v,ee) /\
       expr_post ctx fn cenv cx e es sa sb s0 ee v op u /\
       ptr_val_ok cx (expr_type e) v op G tn u /\
       ghost_inv d cenv cx ee G tn u /\
       ghost_kept cenv es sa G0 tn0 s0 G tn /\
       u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    (irule ifexp_arm_raw_admissible >> simp[]) >>
  qpat_x_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_ptr_def]) >>
  disch_then drule_all >>
  simp[gas_outcome_ptr_def, gas_summary_ptr_at_marked] >>
  strip_tac
  >- (gvs[] >> drule_all ifexp_selected_word_marked >> strip_tac >>
      qexists_tac `marks` >> disj1_tac >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[])
  >- (drule_all ifexp_raw_marked_exception >> strip_tac >>
      qexists_tac `marks` >> disj1_tac >>
      goal_assum (drule_at Any) >> simp[]) >>
  drule ifexp_arm_exempt_transport >> strip_tac >>
  qexists_tac `marks` >> disj2_tac >>
  first_x_assum (qspec_then `cx` assume_tac) >> goal_assum (drule_at Any)
QED

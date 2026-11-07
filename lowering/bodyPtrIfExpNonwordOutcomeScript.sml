Theory bodyPtrIfExpNonwordOutcome
Ancestors bodyPtrIfExpNonwordMarked bodyPtrIfExpWordMarked
  bodyPtrIfExpSource bodyPtrDefs bodySim exprSimHyps exprSimDefs
  gasSummaryComposePtr fragGasPathPtr vyperInterpreter vyperState gasContext

Theorem ifexp_selected_nonword_outcome_ptr:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (IfExp ty c a b) es_outer /\
  (arm = a \/ arm = b) /\ expr_body_pre ce cx env_arm arm es /\
  ~is_word_type ty /\ ~ce.ce_is_ctor /\
  expr_vv_sim_ptr d ctx PG fn ce cx (expr_type arm) arm es /\
  compile_expr ce (expr_type arm) arm sa = (vv,sm) /\
  compile_ifexp_arm ce ty (lowered_value_type ce arm) vv sm = (op,sd) /\
  fn_has_code sa sm fn /\ fn_has_code sm sd fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ ~ctx_has_dalloca ctx /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx arm) (conditional_result cx)) expr_vv_res_ok es /\
  stmt_state_rel ctx fn ce cx es s0 /\ ghost_inv d ce cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
    (bind (eval_expr cx arm) (conditional_result cx)) (es,s0,G0,tn0)
    (\res ee G tn u. ?tv v. res = INL tv /\
       read_result cx tv ee = (INL v,ee) /\
       expr_post ctx fn ce cx arm es sa sd s0 ee v op u /\
       ptr_val_ok cx ty v op G tn u /\ ptr_buf_ok ce (IfExp ty c a b) op G u /\
       ghost_inv d ce cx ee G tn u /\
       ghost_kept ce es sa G0 tn0 s0 G tn /\
       u.vs_current_bb = sd.cs_current_bb /\
       u.vs_inst_idx = LENGTH sd.cs_current_insts)
    (\res ee gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `gas_admissible (eval_expr cx arm) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_vv_gas_admissible] >>
  qpat_x_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_ptr_def]) >>
  disch_then drule_all >>
  simp[gas_outcome_ptr_def, gas_summary_ptr_at_marked] >>
  strip_tac
  >- (qpat_x_assum `r = OK t` SUBST_ALL_TAC >>
      qpat_x_assum `res = INL tv` SUBST_ALL_TAC >>
      drule_all ifexp_selected_nonword_marked >> strip_tac >>
      qexists_tac `marks` >> disj1_tac >>
      goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >> simp[])
  >- (drule_all ifexp_raw_marked_exception >> strip_tac >>
      qexists_tac `marks` >> disj1_tac >> goal_assum (drule_at Any) >> simp[]) >>
  drule ifexp_arm_exempt_transport >> strip_tac >>
  qexists_tac `marks` >> disj2_tac >>
  first_x_assum (qspec_then `cx` assume_tac) >> goal_assum (drule_at Any)
QED

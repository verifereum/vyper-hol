Theory bodyIntCallExprCounted
Ancestors
  bodyIntCallArgCounted bodyIntCallArgPath exprSimDefs loweringPosts
  gasOutcome gasContext loweringSlice compileEnv exprLowering vyperState
  vyperInterpreter venomState

Theorem expr_vv_sim_then_marked:
  expr_vv_sim ctx func cenv cx (expr_type e) e es /\
  compile_expr cenv (expr_type e) e sm = (vv,sn) /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sm.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!left raw mid t.
    gas_marked_exec F (ctx,func) (eval_expr cx e) (es,s0)
      left (INL raw) mid (OK t) /\
    vv_post ctx func cenv cx e es sm sn s0 (mid with gas_obs := []) raw vv t /\
    t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    t.vs_labels = s0.vs_labels ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (k raw : evaluation_state -> unit evaluation_result)
      (mid with gas_obs := [],t) Q
      (\res ee r. ?exc. res = INR exc /\
        expr_exit (INR exc : eval_result + exception) r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) k) (es,s0) Q
    (\res ee r. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) r)
Proof
  strip_tac >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_def] >> disch_then drule_all >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome F _ _ _ _ Post _` >>
  ho_match_mp_tac (gas_outcome_bind_result_marked |>
    Q.INST [`P` |-> `Post`]) >>
  unabbrev_all_tac >>
  rpt conj_tac
  >- (qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
      `(\res (ee : evaluation_state) r. ?exc. res = INR exc /\
          expr_exit (INR exc : eval_result + exception) r) =
        (\res ee r. expr_exit (res : eval_result + exception) r)` by
        (simp[FUN_EQ_THM] >> rpt gen_tac >> Cases_on `res` >> simp[]) >>
      asm_rewrite_tac[]) 
  >- (rpt strip_tac >> gvs[] >>
      drule gas_marked_exec_labels >> disch_tac >>
      first_x_assum irule >> metis_tac[]) >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* Counted index evaluation with a separately supplied readable-base frame. *)
Theory popNestedTargetIndexMemory
Ancestors
  targetSubscriptSplit targetPlaceSimMem exprSimMemDefs exprSimDefs
  loweringPosts targetPlaceSimDefs gasOutcome gasSummary exprSimHypsDefs
  finite_map vyperAST vyperInterpreter vyperState venomState

Theorem pop_nested_target_index_outcome_mem:
  target_post ctx func cenv cx es sa sm s0 es1 pv vt rb t /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es1 /\
  lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es1 /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func t /\
  stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  (!gs v ee. bind (eval_expr cx e) (read_result cx)
       (es1 with gas_obs := gs) = (INL v,ee) ==> place_readable cx ee pv) /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ (!l. FST rb <> Label l) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es1,t)
    (\res ee u. ?v. res = INL v /\
       target_post ctx func cenv cx es sa sn s0 ee pv vt rb u /\
       expr_post ctx func cenv cx e es1 sm sn t ee v ix u /\
       expr_store_bound cx (expr_type e) v ix u /\
       u.vs_current_bb = sn.cs_current_bb /\
       u.vs_inst_idx = LENGTH sn.cs_current_insts /\
       alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_mem_def] >>
  disch_then (qspecl_then [`sm`, `sn`, `ix`, `t`] mp_tac) >>
  impl_tac >- fs[target_post_def] >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- (qexists `marks` >> disj1_tac >> gvs[] >>
      qexistsl [`INL v`, `es_end`, `OK t'`] >> simp[] >>
      `place_readable cx (es_end with gas_obs := []) pv` by
        (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
         simp[gas_marked_exec_def] >> strip_tac >>
         first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
         strip_tac >>
         qpat_x_assum `!gs v ee. _ ==> place_readable _ _ _`
           (drule_then assume_tac) >> gvs[]) >>
      drule_all target_post_index_frame >> simp[])
  >- (qexists `marks` >> disj1_tac >>
      qexistsl [`res`, `es_end`, `r`] >> simp[]) >>
  qexists `marks` >> disj2_tac >> metis_tac[]
QED

(* Counted index execution and target continuation composition. *)
Theory targetIndexCompositionMemory
Ancestors
  targetMemoryContracts targetSubscriptSplit exprSimMemDefs
  loweringPosts gasOutcome gasSummary gasContext fragGasMode
  exprSimDefs exprLowering compileEnv vyperInterpreter vyperState
  loweringStateRelDefs venomState list finite_map gasStorage vyperStorageTrace
  vyperStorageFootprint stmtSimProps

Theorem target_index_outcome_mem:
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
    target_post H ctx func cenv cx es sa sm s0 es1 pv vt rb t /\
    stmt_state_rel H ctx func cenv cx es s0) /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es1 /\
  lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es1 /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  (!gs v ee. bind (eval_expr cx e) (read_result cx)
       (es1 with gas_obs := gs) = (INL v,ee) ==> place_readable cx ee pv) /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ (!l. FST rb <> Label l) /\
  alloca_history func t ==>
  gas_outcome T (cx_tops cx) (ctx,func) cx st0
    (bind (eval_expr cx e) (read_result cx)) (es1,t)
    (\H res ee u. ?v. res = INL v /\
       target_post H ctx func cenv cx es sa sn s0 ee pv vt rb u /\
       expr_post H ctx func cenv cx e es1 sm sn t ee v ix u /\
       expr_store_bound cx (expr_type e) v ix u /\
       u.vs_current_bb = sn.cs_current_bb /\
       u.vs_inst_idx = LENGTH sn.cs_current_insts /\
       alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next)
    (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  strip_tac >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_mem_def] >>
  disch_then (qspecl_then [`st0`, `sm`, `sn`, `ix`, `t`] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H es1.storage_trace ==> _` drule >>
      simp[target_post_def]) >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> BETA_TAC >> strip_tac
  >- (qexists `marks` >> disj1_tac >> first_assum ACCEPT_TAC)
  >- (qexists `marks` >> disj2_tac >> disj1_tac >> gvs[] >>
      qexistsl [`res`, `es_end`, `OK t'`] >> simp[] >> disj1_tac >>
      rpt strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> _`
        (drule_then strip_assume_tac) >> gvs[] >>
      `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
        (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
         simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
              vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
      `valid_horizon cx st0 H es1.storage_trace` by
        (drule_all gas_marked_exec_valid_prefix >> simp[]) >>
      qpat_x_assum `!H. valid_horizon _ _ H es1.storage_trace ==> _`
        (drule_then strip_assume_tac) >>
      `place_readable cx (es_end with gas_obs := []) pv` by
        (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
         simp[gas_marked_exec_def] >> strip_tac >>
         first_x_assum (qspec_then `[]` strip_assume_tac) >>
         qpat_x_assum `!gs v ee. _ = _ ==> place_readable _ _ _` drule >>
         simp[]) >>
      drule_all target_post_index_frame >> simp[])
  >- (qexists `marks` >> disj2_tac >> disj1_tac >>
      qexistsl [`res`, `es_end`, `r`] >> simp[] >> disj2_tac >>
      rpt strip_tac >>
      qpat_x_assum `!H. _ ==> expr_exit _ _ /\ _` (qspec_then `H` mp_tac) >>
      simp[halt_exit_def, halt_rel_def, accounts_rel_def]) >>
  qexists `marks` >> disj2_tac >> disj2_tac >> metis_tac[]
QED

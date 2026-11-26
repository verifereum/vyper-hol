(* Select the RHS run using the actual paired assignment compiler cuts. *)
Theory bodyAssignPlaceRhsDispatchMods
Ancestors
  bodyQualifiedPlaceEmptyRhsMods bodyQualifiedPlaceSnapshotRhsMods
  bodyQualifiedPlaceRawRhsMods bodyQualifiedPlaceTargetEntryMods
  bodyQualifiedPlaceRhsPostMods bodyAssignQualifiedStageJoinMods
  bodyAssignLocalPlaceRoutesMods bodyFullPredsMods loweringPosts
Libs
  monadsyntax

Theorem assign_place_rhs_dispatch_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es /\
  body_expr_full_ok_mods mods exps cx e /\
  stmt_exprs_ok cenv (Assign (BaseTarget bt) e) /\
  type_widens_to env.type_defs (expr_type e) dty /\
  qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb saved sr st
    shadow_sr shadow_st dst /\
  gas_shadow_state sa shadow_sa /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ret_pc_ok cenv sa s0 /\ return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst t. frag_reachable ctx func s0 fn inst t ==> dalloca_fmp_headroom inst t) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res mid Gu tu u. ?v. res = INL v /\
      qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods cenv cx env bt e dty
        es sa shadow_sa sr shadow_sr saved s0 G0 tn0 H v mid Gu tu u)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> disch_tac >>
  Cases_on `has_length_word (expr_type e) /\ is_empty_value_expr e`
  >- (qpat_x_assum `has_length_word _ /\ is_empty_value_expr _` strip_assume_tac >>
      irule qualified_place_empty_rhs_mods >>
      qpat_assum `qualified_assign_code_mods _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all_then strip_assume_tac qualified_place_code_intervals_mods >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  Cases_on `expr_can_mutate cenv (target_to_expr bt)`
  >- (irule qualified_place_snapshot_rhs_mods >>
      qpat_assum `qualified_assign_code_mods _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
      qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
      qpat_assum `gas_shadow_function _ _` (irule_at Any) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `qualified_assign_code_mods _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_code_mods_def]) >>
  `?vv. saved = SOME vv` by
    (drule_then strip_assume_tac qualified_assign_rhs_code_view_mods >> fs[]) >>
  qpat_x_assum `saved = SOME _` SUBST_ALL_TAC >>
  irule qualified_place_raw_rhs_mods >>
  qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `gas_shadow_function _ _` (irule_at Any) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(*
 * A target walk whose indices can't mutate keeps the source machine state.
 *
 * Assign evaluates its RHS first and then the target's place
 * (eval_base_place, compiled by compile_get_target_ptr).  When no index of
 * the target can mutate (~expr_can_mutate: internal calls only to view or
 * pure functions, external calls only static), the walk leaves the
 * accounts, transient storage, immutables and pending deletions
 * (machine_frame up to logs) and the scopes as they were, next to the
 * walk's own target_post from target_sim.  Logs may grow: a raw_log in
 * an index counts as non-mutating.  Internal calls are tied to the module's
 * declared mutability by ce_func_mutability and function_mutability_ok.
 *
 * TOP-LEVEL:
 *   target_walk_frame
 *)
Theory targetPureWalkFrame
Ancestors
  targetPlaceSimDefs loweringStateRelDefs loweringPosts gasOutcome gasContext
  stmtLowering exprLowering compileVyper vyperTypeContract vyperTypeCallGraph
  vyperMachineFrame targetPureWalkSource targetPureWalkScopes

Theorem target_walk_frame:
  !ctx func cenv cx env bt es vt sa sb op s0.
    ~expr_can_mutate cenv (target_to_expr bt) /\
    cenv.ce_func_mutability = build_func_mutability (cx_tops cx) /\
    (!vis mut nr rr fn args dflts ret body.
       MEM (FunctionDecl vis mut nr rr fn args dflts ret body) (cx_tops cx) ==>
       function_mutability_ok [(NONE, cx_tops cx)] vis mut nr dflts body) /\
    get_module_code cx NONE = SOME (cx_tops cx) /\
    EVERY (\c. FST c = NONE /\
               supported_program (cx_tops cx) /\
               IS_SOME (supported_function_decl (cx_tops cx) c Internal))
      (int_calls_target bt) /\
    target_sim ctx func cenv cx env bt es /\
    type_place_target env bt = SOME vt /\
    compile_get_target_ptr compile_expr cenv bt sa = (op, sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    gas_admissible (eval_base_place cx bt) target_res_ok es /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx, func) (eval_base_place cx bt) (es, s0)
      (\res ee t. ?pv. res = INL pv /\
         target_post ctx func cenv cx es sa sb s0 ee pv vt op t /\
         machine_frame (es with logs := ee.logs) ee /\ ee.scopes = es.scopes /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >>
  `gas_outcome F (cx_tops cx) (ctx,func) (eval_base_place cx bt) (es,s0)
    (\res ee t. ?pv. res = INL pv /\
      target_post ctx func cenv cx es sa sb s0 ee pv vt op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)` by
    metis_tac[target_sim_def] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gasSummaryTheory.gas_summary_at_def])
      >- ( gvs[] >>
           rename1 `target_post ctx func cenv cx es sa sb s0 _ pv vt op t` >>
           `eval_base_place cx bt
              (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
              (INL pv, es_end with gas_obs := [])` by
             (fs[gasSummaryTheory.gas_marked_exec_def] >>
              first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
           `machine_frame (es with logs := es_end.logs) es_end` by
             (drule_all target_walk_source_frame >>
              simp[machine_frame_def]) >>
           `es_end.scopes = es.scopes` by
             (drule_all target_walk_scopes >> simp[]) >>
           rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
           simp[gasSummaryTheory.gas_summary_at_def] >>
           qexistsl_tac [`INL pv`, `es_end`, `OK t`] >>
           gvs[machine_frame_def]) >>
      rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
      simp[gasSummaryTheory.gas_summary_at_def] >> metis_tac[]) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj2_tac >>
  metis_tac[]
QED

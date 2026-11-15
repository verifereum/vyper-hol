(*
 * A target walk whose indices can't mutate keeps an earlier value's post.
 *
 * Assign evaluates its RHS e first and computes the target's pointer
 * after (eval_stmt, compile_stmt).  When no index of the target can mutate
 * (~expr_can_mutate), the walk (eval_base_place, compile_get_target_ptr)
 * keeps the source machine state and scopes (target_walk_frame), so it
 * changes the source state only in its oracle fields, and its code writes
 * neither the memory of the live locals and earlier allocations nor
 * storage, transient storage, immutables, accounts or code.  So e's value
 * post (vv_post), whatever e is, holds again after the walk, rebased to the
 * walk's end state, next to the walk's own target_post and the frame
 * (wb_frame) from e's start.
 *
 * TOP-LEVEL:
 *   target_walk_vv_frame
 *)

Theory targetWalkVvFrame
Ancestors
  targetPlaceSimDefs loweringPosts targetPurePostTransport targetPureWalkFrame
  stmtLoweringMono gasOutcome gasSummary gasContext vyperMachineFrame vyperState
  stmtLowering exprLowering compileVyper vyperTypeContract vyperTypeCallGraph
  vyperStorageFootprint vyperStorageTrace gasStorage

Theorem target_walk_vv_frame:
  !ctx func cx cenv env bt e es es1 st0 vt sa sm sb s0 s1 tv vv op.
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
    target_sim ctx func cenv cx env bt es1 /\
    type_place_target env bt = SOME vt /\
    (!H. valid_horizon cx st0 H es1.storage_trace ==>
      vv_post H ctx func cenv cx e es sa sm s0 es1 tv vv s1 /\
      vv_storage_live H cx vv es1 s1 /\
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es1 (FST H)) /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!l. vv_operand vv <> Label l) /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    local_ptrs_reserved cenv sa /\
    compile_get_target_ptr compile_expr cenv bt sm = (op, sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sm /\
    gas_admissible (eval_base_place cx bt) target_res_ok es1 /\
    ~s1.vs_halted /\
    s1.vs_current_bb = sm.cs_current_bb /\
    s1.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx, func) cx st0 (eval_base_place cx bt) (es1, s1)
      (\H res ee t. ?pv. res = INL pv /\
         target_post H ctx func cenv cx es1 sm sb s1 ee pv vt op t /\
         vv_post H ctx func cenv cx e ee sa sb t ee tv vv t /\
         wb_frame cenv es ee sa s0 t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  rpt strip_tac >>
  `sm.cs_next_id <= sb.cs_next_id` by
    (qspec_then `bt` (qspecl_then [`cenv`, `sm`] mp_tac)
       ci_mono_compile_get_target_ptr >> simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `!H. valid_horizon cx st0 H es1.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es1 s1 /\
      storage_well_formed_on cx es1 (FST H)` by
    (rpt strip_tac >> first_x_assum drule >> simp[vv_post_def]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `env`, `bt`, `es1`, `st0`,
               `vt`, `sm`, `sb`, `op`, `s1`] mp_tac target_walk_frame >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> simp[])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- suspend "normal" >>
      rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >>
      disj2_tac >> disj1_tac >> simp[gas_summary_at_def] >>
      qexistsl_tac [`res`, `es_end`, `r`] >> fs[] >>
      disj2_tac >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Resume target_walk_vv_frame[normal]:
  gvs[] >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >>
  disj2_tac >> disj1_tac >> simp[gas_summary_at_def] >>
  qexistsl_tac [`res`, `es_end`, `OK t`] >> simp[] >>
  disj1_tac >>
  gen_tac >> disch_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> ?pv. _`
    (qspec_then `H` mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  `eval_base_place cx bt
      (es1 with gas_obs := gas_explicit marks s1.vs_gas_readings) =
      (INL pv, es_end with gas_obs := [])` by
    (fs[gas_marked_exec_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `valid_horizon cx st0 H es1.storage_trace` by
    (`storage_trace_frame (eval_base_place cx bt)` by
       simp[evaluate_storage_trace_frame] >>
     drule_all storage_trace_frame_prefix >> simp[] >>
     strip_tac >> gvs[] >> fs[valid_horizon_def]) >>
  `vv_post H ctx func cenv cx e es sa sm s0 es1 tv vv s1 /\
   vv_storage_live H cx vv es1 s1 /\
   stmt_state_rel H ctx func cenv cx es s0` by metis_tac[] >>
  `?gs os rq lg st. es_end with gas_obs := [] =
      es1 with <|gas_obs := gs; outcomes := os; requests := rq;
                 logs := lg; storage_trace := st|>` by
    fs[machine_frame_def, evaluation_state_component_equality] >>
  `vv_post H ctx func cenv cx e (es_end with gas_obs := []) sa sb t
      (es_end with gas_obs := []) tv vv t /\
   wb_frame cenv es (es_end with gas_obs := []) sa s0 t` by
    (irule target_saved_post_transport >> metis_tac[]) >>
  simp[]
QED

Finalise target_walk_vv_frame

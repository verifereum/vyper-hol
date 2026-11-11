(*
 * A pure target walk keeps an earlier value's post.
 *
 * Assign evaluates its RHS e first and computes the target's pointer
 * after (eval_stmt, compile_stmt).  When the target's indices are pure
 * (supported_target_pure: no internal calls, no pop()), the walk
 * (eval_base_place, compile_get_target_ptr) changes the source state only
 * in its gas observations, and its code writes neither the memory of the
 * live locals and earlier allocations nor storage, transient storage,
 * immutables, accounts or code.  So e's value post (vv_post), whatever e
 * is, holds again after the walk, next to the walk's own target_post.
 *
 * TOP-LEVEL:
 *   target_pure_vv_frame
 *)

Theory targetPureVvFrame
Ancestors
  targetPureWalkFrame targetPlaceSimDefs supportedTargets loweringPosts targetPurePostTransport
  targetPureSourceFrame stmtLoweringMono gasOutcome gasSummary

Theorem target_pure_vv_frame:
  !ctx func cx cenv env tops bt e es es1 vt sa sm sb s0 s1 tv vv op.
    supported_target_pure tops bt /\
    target_sim ctx func cenv cx env bt es1 /\
    type_place_target env bt = SOME vt /\
    vv_post ctx func cenv cx e es sa sm s0 es1 tv vv s1 /\
    vv_storage_live cx vv es1 s1 /\
    (cenv.ce_is_ctor ==> vv_location vv <> SOME LocCode) /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!l. vv_operand vv <> Label l) /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    compile_get_target_ptr compile_expr cenv bt sm = (op, sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sm /\
    gas_admissible (eval_base_place cx bt) target_res_ok es1 /\
    ~s1.vs_halted /\
    s1.vs_current_bb = sm.cs_current_bb /\
    s1.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx, func) (eval_base_place cx bt) (es1, s1)
      (\res ee t. ?pv. res = INL pv /\
         target_post ctx func cenv cx es1 sm sb s1 ee pv vt op t /\
         vv_post ctx func cenv cx e es sa sb s0 ee tv vv t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)
Proof
  rpt strip_tac >>
  `sm.cs_next_id <= sb.cs_next_id` by
    (qspec_then `bt` (qspecl_then [`cenv`, `sm`] mp_tac)
       ci_mono_compile_get_target_ptr >> simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `stmt_state_rel ctx func cenv cx es1 s1` by gvs[vv_post_def] >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `env`, `tops`, `bt`, `es1`, `vt`,
               `sm`, `sb`, `op`, `s1`] mp_tac target_pure_walk_pure_frame >>
  simp[] >>
  disch_then (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- suspend "normal"
      >> suspend "exit") >>
  suspend "exempt"
QED

Resume target_pure_vv_frame[normal]:
  gvs[] >>
  `?gs os. es_end with gas_obs := [] =
      es1 with <|gas_obs := gs; outcomes := os|>` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` assume_tac) >>
     drule_all target_pure_base_source_frame >> simp[]) >>
  `vv_post ctx func cenv cx e es sa sb s0
      (es_end with gas_obs := []) tv vv t` by
    (irule target_saved_post_transport >> metis_tac[]) >>
  simp[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL pv`, `es_end`, `OK t`] >> gvs[]
QED

Resume target_pure_vv_frame[exit]:
  simp[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
  simp[gas_summary_at_def] >> metis_tac[]
QED

Resume target_pure_vv_frame[exempt]:
  simp[gas_outcome_def] >> qexists_tac `marks` >> disj2_tac >> metis_tac[]
QED

Finalise target_pure_vv_frame

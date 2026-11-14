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

Theorem target_walk_vv_frame:
  !ctx func cx cenv env bt e es es1 vt sa sm sb s0 s1 tv vv op.
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
    vv_post ctx func cenv cx e es sa sm s0 es1 tv vv s1 /\
    vv_storage_live cx vv es1 s1 /\
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
         vv_post ctx func cenv cx e ee sa sb t ee tv vv t /\
         wb_frame cenv es ee sa s0 t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)
Proof
  rpt strip_tac >>
  `sm.cs_next_id <= sb.cs_next_id` by
    (qspec_then `bt` (qspecl_then [`cenv`, `sm`] mp_tac)
       ci_mono_compile_get_target_ptr >> simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `stmt_state_rel ctx func cenv cx es1 s1` by gvs[vv_post_def] >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `env`, `bt`, `es1`, `vt`,
               `sm`, `sb`, `op`, `s1`] mp_tac target_walk_frame >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- suspend "normal"
      >> suspend "exit") >>
  suspend "exempt"
QED

Resume target_walk_vv_frame[normal]:
  gvs[] >>
  `?gs os rq lg. es_end with gas_obs := [] =
      es1 with <|gas_obs := gs; outcomes := os; requests := rq; logs := lg|>` by
    fs[machine_frame_def, evaluation_state_component_equality] >>
  `vv_post ctx func cenv cx e (es_end with gas_obs := []) sa sb t
      (es_end with gas_obs := []) tv vv t /\
   wb_frame cenv es (es_end with gas_obs := []) sa s0 t` by
    (irule target_saved_post_transport >> metis_tac[]) >>
  simp[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL pv`, `es_end`, `OK t`] >> gvs[]
QED

Resume target_walk_vv_frame[exit]:
  simp[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
  simp[gas_summary_at_def] >> metis_tac[]
QED

Resume target_walk_vv_frame[exempt]:
  simp[gas_outcome_def] >> qexists_tac `marks` >> disj2_tac >> metis_tac[]
QED

Finalise target_walk_vv_frame

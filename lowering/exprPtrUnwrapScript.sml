(*
 * The pointer twins of exprSimUnwrap's expr_sim_of_vv_sim and
 * exprSimStack's expr_vv_sim_stack: an expression's located or stack
 * value gives its lowered value, with the ghost.  The compound
 * expression cases (bodyPtrExprCases) prove one of expr_sim_ptr and
 * expr_vv_sim_ptr and take the other from these.
 *
 * TOP-LEVEL:
 *   expr_sim_ptr_of_vv -- expr_vv_sim_ptr gives expr_sim_ptr
 *   expr_vv_sim_ptr_stack -- expr_sim_ptr gives expr_vv_sim_ptr when
 *     compile_expr leaves a stack value
 *)
Theory exprPtrUnwrap
Ancestors
  bodyPtrDefs fragGasPathPtr exprSimStack exprSimDefs exprSimHyps loweringPosts
  gasExemptCert exprLowering emitHelper compileEnv vyperInterpreter vyperState

(* exprSimStack's expr_stack_outcome with the ghost: a raw value's outcome
   is its forced value's, the post read through Value. *)
Theorem expr_stack_outcome_ptr:
  (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) /\
  gas_outcome_ptr D tops (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\res ee G tn u. ?v. res = INL v /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ee G tn u /\
      ptr_val_ok cx (expr_type e) v op G tn u /\
      (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op G u) /\
      ghost_kept cenv es sa G0 tn0 s0 G tn)
    (\res ee gt r. expr_exit res r) ==>
  gas_outcome_ptr D tops (ctx,func) PG (eval_expr cx e) (es,s0,G0,tn0)
    (\res ee G tn u. ?tv. res = INL tv /\
      vv_post ctx func cenv cx e es sa sb s0 ee tv (StackValue t op) u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ee G tn u /\
      ptr_vv_ok cx (expr_type e) tv (StackValue t op) ee G tn u /\
      (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op G u) /\
      ghost_kept cenv es sa G0 tn0 s0 G tn)
    (\res ee gt r. expr_exit res r)
Proof
  rw[gas_outcome_ptr_def] >> qexists_tac `marks`
  >- (disj1_tac >> gvs[gas_summary_ptr_at_def]
      >- (qexistsl_tac [`INL (Value v)`, `es_end`, `G`, `tn`, `OK u`] >>
          simp[] >> conj_tac
          >- (gen_tac >> drule eval_expr_force_value >>
              disch_then (qspec_then `es with gas_obs :=
                gas_explicit marks s0.vs_gas_readings ++ tail` mp_tac) >>
              simp[]) >>
          gvs[expr_post_def, vv_post_def, vv_holds_def, vv_at_def, vv_own_def,
              ptr_vv_ok_def, read_result_def, return_def] >>
          first_assum ACCEPT_TAC) >>
      qexistsl_tac [`case res of INL v => INL (Value v) | INR ex => INR ex`,
                    `es_end`, `G`, `tn`, `r`] >>
      simp[expr_exit_success_map] >> gen_tac >>
      drule eval_expr_force_value >>
      disch_then (qspec_then `es with gas_obs :=
        gas_explicit marks s0.vs_gas_readings ++ tail` mp_tac) >> simp[]) >>
  disj2_tac >> drule eval_expr_force_ignore >>
  disch_then (fn th => fs[th]) >> metis_tac[]
QED

(* unwrap_value's code takes vv_post and ptr_vv_ok to expr_post and
   ptr_val_ok.  expr_body_pre gives exprSimUnwrap's side condition
   (exprSimHyps' expr_body_pre_copy_ok) and, on success, that the type
   evaluates (exprSimSource's expr_body_pre_runtime_typed), which the
   loaded word's taint needs: ptr_vv_ok's memory clause says nothing about
   a type that doesn't evaluate. *)
Theorem expr_sim_ptr_of_vv:
  !d ctx PG func cenv cx env ty e es.
    expr_body_pre cenv cx env e es /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty e es ==>
    expr_sim_ptr d ctx PG func cenv cx ty e es
Proof
  cheat
QED

Theorem expr_vv_sim_ptr_stack:
  !d ctx PG func cenv cx ty e es.
    expr_sim_ptr d ctx PG func cenv cx ty e es /\
    (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op, sb)) /\
    (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty e es
Proof
  rw[expr_vv_sim_ptr_def] >>
  qpat_x_assum `!sa. ?t op sb. _` (qspec_then `sa` strip_assume_tac) >> gvs[] >>
  `lower_value compile_expr cenv ty e sa = (op, sb)` by
    simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[eval_expr_force_admissible] >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`sa`, `sb`, `op`, `s0`, `G0`, `tn0`] mp_tac) >>
  simp[] >> strip_tac >>
  irule expr_stack_outcome_ptr >> conj_tac >> first_assum ACCEPT_TAC
QED

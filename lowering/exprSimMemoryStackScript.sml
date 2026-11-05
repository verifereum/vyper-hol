(* Stack adaptation retains counted memory execution and complete posts. *)
Theory exprSimMemoryStack
Ancestors
  exprSimMemDefs exprSimDefs exprSimStack loweringPosts gasOutcome gasSummary
  gasSummaryCompose gasContext gasExemptCert exprLowering emitHelper compileEnv
  vyperInterpreter vyperState fragExecMem

Theorem expr_stack_outcome_mem:
  (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) /\
  (~is_word_type (expr_type e) ==>
   !tvt. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tvt ==>
         type_memory_size tvt = 0) /\
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
    (\res ee u. ?v. res = INL v /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
      expr_store_bound cx (expr_type e) v op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next)
    (\res ee r. expr_exit res r) ==>
  gas_outcome T (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s0)
    (\res ee u. ?tv. res = INL tv /\
      vv_post ctx func cenv cx e es sa sb s0 ee tv (StackValue t op) u /\
      vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv (StackValue t op) u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  rw[gas_outcome_def] >> qexists_tac `marks`
  >- (disj1_tac >>
      gvs[gas_summary_at_def, gas_marked_exec_def]
      >- (qexistsl_tac [`INL (Value v)`, `es_end`, `OK u`] >>
          simp[] >> conj_tac
          >- (gen_tac >> drule eval_expr_force_value >>
              disch_then (qspec_then `es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail` mp_tac) >> simp[]) >>
          gvs[expr_post_def, vv_post_def, vv_holds_def, vv_at_def,
              read_result_def, return_def] >>
          conj_tac >- first_assum ACCEPT_TAC >>
          irule vv_store_bound_stack_value >> conj_tac >>
          first_assum ACCEPT_TAC) >>
      qexistsl_tac [`case res of INL v => INL (Value v) | INR ex => INR ex`,
                   `es_end`, `r`] >>
      simp[expr_exit_success_map] >> gen_tac >>
      drule eval_expr_force_value >> disch_then (qspec_then `es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail` mp_tac) >> simp[]) >>
  disj2_tac >> drule eval_expr_force_ignore >>
  disch_then (fn th => fs[th]) >> metis_tac[]
QED

(* A non-word stack result's lowered type must have zero size: its operand
   is bounded only by the value's footprint. *)
Theorem body_expr_vv_sim_mem_stack:
  (~is_word_type (expr_type e) ==>
   !tvt. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tvt ==>
         type_memory_size tvt = 0) ==>
  expr_sim_mem ctx func cenv cx ty e es /\
  (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op,sb)) /\
  (!s tv es'. eval_expr cx e s = (INL tv,es') ==> ?v. tv = Value v) ==>
  expr_vv_sim_mem ctx func cenv cx ty e es
Proof
  rw[expr_vv_sim_mem_def] >>
  qpat_x_assum `!sa. ?t op sb. _` (qspec_then `sa` strip_assume_tac) >> gvs[] >>
  `lower_value compile_expr cenv ty e sa = (op,sb)` by
    simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  irule expr_stack_outcome_mem >> rpt conj_tac
  >- (first_assum ACCEPT_TAC)
  >- (first_assum ACCEPT_TAC) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[eval_expr_force_admissible] >>
  gvs[expr_sim_mem_def] >> first_x_assum irule >> simp[]
QED

Theorem body_expr_vv_sim_mem_stack_word:
  is_word_type (expr_type e) ==>
  expr_sim_mem ctx func cenv cx ty e es /\
  (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op,sb)) /\
  (!s tv es'. eval_expr cx e s = (INL tv,es') ==> ?v. tv = Value v) ==>
  expr_vv_sim_mem ctx func cenv cx ty e es
Proof
  rpt strip_tac >> irule body_expr_vv_sim_mem_stack >> simp[] >> metis_tac[]
QED

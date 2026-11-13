(* Normal counted prefixes introduce the shared expression judgment. *)
Theory exprSimValues
Ancestors
  exprSimDefs gasNormalPrefix gasOutcome gasSummary gasContext
  loweringPosts exprLowering emitHelper compileEnv loweringSlice vyperState

Theorem expr_sim_values:
  !ctx func cenv cx ty e es.
    (!sa sb op s0.
       lower_value compile_expr cenv ty e sa = (op, sb) /\
       fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
       local_ptrs_reserved cenv sa /\
       gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
       stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
       s0.vs_current_bb = sa.cs_current_bb /\
       s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
       ?marks v ee t.
         gas_value_prefix F (ctx,func,cenv,cx) (ty,e)
           (sa,sb,op) (es,s0) marks (v,ee,t)) ==>
    expr_sim ctx func cenv cx ty e es
Proof
  rw[expr_sim_def] >> first_x_assum drule_all >>
  simp[gas_value_prefix_def] >> rpt strip_tac >>
  PURE_REWRITE_TAC[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
  PURE_REWRITE_TAC[gas_summary_at_def] >>
  qexistsl_tac [`INL v`, `ee`, `OK t`] >> simp[]
QED

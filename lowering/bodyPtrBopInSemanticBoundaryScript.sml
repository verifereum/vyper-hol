(* S1 necessary semantic condition for any genuine expression entry.
   No pointer-main theorem is used by this boundary. *)
Theory bodyPtrBopInSemanticBoundary
Ancestors bodySimMain exprSimDefs

Theorem body_entry_semantic_outcome:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
  lower_value compile_expr cenv ty e sa = (op, sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx, func)
    (bind (eval_expr cx e) (read_result cx)) (es, s0)
    (\res ee t. ?v. res = INL v /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> drule_all body_expr_sim >>
  disch_then (qspecl_then [`func`, `ty`] strip_assume_tac) >>
  gvs[expr_sim_def] >> first_x_assum drule >> simp[]
QED

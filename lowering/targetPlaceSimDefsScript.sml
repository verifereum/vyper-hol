(* Counted place-target simulation over actual source evaluation. *)
Theory targetPlaceSimDefs
Ancestors
  exprSimDefs loweringPosts gasOutcome gasContext exprLowering stmtLowering
  compileEnv exprLoweringProps vyperInterpreter vyperState vyperTypeSystem
  venomState

Definition target_res_ok_def:
  target_res_ok (res : eval_result + exception) <=>
    (?pv. res = INL pv) \/ (?m. res = INR (Error (RuntimeError m))) \/
    (?d. res = INR (Error (RevertData d))) \/
    (?str. res = INR (AssertException str))
End

Definition target_sim_def:
  target_sim ctx func cenv cx env bt es <=>
    !vt sa sb op s0.
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
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts)
        (\res ee r. expr_exit res r)
End

(* Physical source interface before evaluating an assignment's target. *)
Theory placeRelayoutPhysicalSource
Ancestors
  placeRelayoutRawSource exprSimIfExpWidenedCounted loweringPosts
  exprLowering context compileEnv vyperInterpreter vyperState

Theorem strict_widened_vv_physical_source:
  vv_post ctx func cenv cx e es sa sb s0 ee (Value v) vv s /\
  compile_expr cenv ty e si = (vv,sj) /\
  post_value_type cenv e <> expr_type e /\
  ~is_word_type (post_value_type cenv e) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME stv ==>
  (!sm. unwrap_value cenv vv sm = (vv_operand vv,sm)) /\
  expr_val_own cenv cx (post_value_type cenv e) sa sb ee v (vv_operand vv) s /\
  expr_val_rel cx (post_value_type cenv e) v (vv_operand vv) s /\
  val_wf stv v /\
  ?w. eval_operand (vv_operand vv) s = SOME w /\
      val_in_memory stv v (w2n w) s.vs_memory
Proof
  strip_tac >> drule_all compile_changed_physical_unwrap_shape >> strip_tac >>
  gvs[vv_operand_def, unwrap_value_def, comp_return_def,
      vv_post_def, vv_holds_def, vv_at_def, vv_own_def,
      expr_val_own_def, expr_val_at_def, expr_val_rel_def,
      read_result_def, return_def] >>
  metis_tac[]
QED

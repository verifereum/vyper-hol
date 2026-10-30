(*
 * compile_expr keeps its block open: lower_value over a child
 *
 * TOP-LEVEL:
 *   lower_value_child_open, lower_value_list_head_open — lower_value of
 *     a child that compiles open is open
 *)

Theory exprOpenChild
Ancestors
  exprOpenTerminals exprLowering exprCallBounds compileEnv list

Theorem lower_value_child_open:
  !bound cfn cenv aty e sa v sb.
    expr_size e < bound /\
    (!vv st. cfn cenv aty e sa = (vv,st) ==> ~block_is_terminated st) /\
    lower_value (expr_child_callback bound cfn) cenv aty e sa = (v,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[lower_value_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  gvs[expr_child_callback_valid] >>
  drule_all unwrap_value_open >> simp[]
QED

Theorem lower_value_list_head_open:
  !cfn cenv aty e es sa v sb.
    (!vv st. cfn cenv aty e sa = (vv,st) ==> ~block_is_terminated st) /\
    lower_value (expr_child_callback (list_size expr_size (e::es)) cfn)
      cenv aty e sa = (v,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> strip_tac >> irule lower_value_child_open >>
  goal_assum (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  simp[] >> metis_tac[expr_list_member_bound, MEM]
QED

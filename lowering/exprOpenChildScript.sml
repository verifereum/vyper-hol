(*
 * compile_expr keeps its block open: lower_value over a child
 *
 * TOP-LEVEL:
 *   lower_value_child_open — lower_value of a child that compiles open
 *     is open
 *)

Theory exprOpenChild
Ancestors
  exprOpenTerminals exprLowering exprCallBounds compileEnv list

Theorem lower_value_child_open:
  !bound cfn cenv aty e sa v sb.
    expr_size e + cenv_defaults_size cenv < bound /\
    (!vv st. cfn cenv aty e sa = (vv,st) ==> ~block_is_terminated st) /\
    lower_value (expr_child_callback bound cfn) cenv aty e sa = (v,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[lower_value_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  gvs[expr_child_callback_valid] >>
  drule_all unwrap_value_open >> simp[]
QED

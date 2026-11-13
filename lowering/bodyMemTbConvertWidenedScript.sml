(*
 * HELD for the posts-interface (post_value_type) wave: the memory twin of
 * bodySimConvertWidened's body_convert_widened_call_arg, the conversion of
 * an internal call whose type widens its callee's return type.
 *
 * body_convert_widened_call_arg_mem is the case bodyMemTbConvert's
 * body_type_builtin_convert_mem_case splits off.
 *)
Theory bodyMemTbConvertWidened
Ancestors
  bodyMemoryPreds bodyMemTbConvertCallLift bodyMemTbConvertScalarBranch
  exprSimHyps exprSimHypsDefs exprSimConvert exprLowering vyperAST

(* The conversion's lowering sizes the operand by the callee's return type,
   so describing the operand's value at that type is the internal-call
   simulation's work, as in S1. *)
Theorem body_convert_widened_call_arg_mem:
  !cx v11 typ e1.
    body_exprs_mem_ok cx [e1] ==>
    !tops ctx func cenv env ty st.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (TypeBuiltin v11 Convert typ [e1]) st /\
      (?a f cargs d. e1 = Call a (IntCall f) cargs d) /\
      lowered_value_type cenv e1 <> expr_type e1 ==>
      expr_sim_mem ctx func cenv cx ty (TypeBuiltin v11 Convert typ [e1]) st /\
      expr_vv_sim_mem ctx func cenv cx ty (TypeBuiltin v11 Convert typ [e1]) st
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule expr_body_pre_convert >> strip_tac >>
  `expr_sim_mem ctx func cenv cx (expr_type e1) e1 st /\
   expr_vv_sim_mem ctx func cenv cx (expr_type e1) e1 st` by
    (gvs[body_exprs_mem_ok_def] >> metis_tac[body_expr_mem_ok_def]) >>
  Cases_on `is_bytestring_type typ`
  >- (irule call_bytestring_convert_mem >> metis_tac[]) >>
  Cases_on `is_bytestring_type (expr_type e1)`
  >- (irule call_dynamic_convert_mem >> metis_tac[]) >>
  irule scalar_convert_branch_mem >> metis_tac[]
QED

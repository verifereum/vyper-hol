(*
 * The pointer twin of S1's bodySimConvertWidened: a conversion whose
 * operand is an internal call whose type widens its callee's return type,
 * for bodyPtrTypeBuiltins' type_builtin_expr_ptr_ok.
 *
 * RESIDUAL, HELD with S1's body_convert_widened_call_arg: describing the
 * operand's value at the callee's return type is the internal-call
 * simulation's work.  Not open work here.
 *
 * TOP-LEVEL:
 *   body_convert_widened_call_arg_ptr - that case
 *)
Theory bodyPtrTypeBuiltinsConvertWidened
Ancestors
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

(* RESIDUAL: widened internal-call Convert operand, held with S1's
   body_convert_widened_call_arg *)
Theorem body_convert_widened_call_arg_ptr:
  !cx v11 typ e1.
    body_exprs_ptr_ok cx [e1] ==>
    !d PG tops ctx func cenv env ty st.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (TypeBuiltin v11 Convert typ [e1]) st /\
      (?a f cargs drv. e1 = Call a (IntCall f) cargs drv) /\
      lowered_value_type cenv e1 <> expr_type e1 ==>
      expr_sim_ptr d ctx PG func cenv cx ty (TypeBuiltin v11 Convert typ [e1]) st /\
      expr_vv_sim_ptr d ctx PG func cenv cx ty (TypeBuiltin v11 Convert typ [e1]) st
Proof
  cheat
QED

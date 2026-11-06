(*
 * HELD for the posts-interface (post_value_type) wave: the conversion of
 * an internal call whose type widens its callee's return type.
 *
 * body_convert_widened_call_arg, the case bodySimExprCases'
 * body_type_builtin_case splits off for compile_type_builtin_case.
 *)

Theory bodySimConvertWidened
Ancestors
  exprSimSource
  exprSimHypsDefs
  list bodySim  exprSimHyps exprSimOperators exprSimAttribute
  exprSimPlaces exprSimPopNested targetPlaceSim exprSimAggregates exprSimSend exprSimMain exprSimECArith vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph

(* A conversion whose operand is an internal call whose type widens its
   callee's return type: the conversion's lowering sizes the operand by the
   callee's return type, so, as for body_struct_lit_widened_call_elem,
   describing the operand's value at that type is the internal-call
   simulation's work (body_intcall_case). *)
Theorem body_convert_widened_call_arg:
  !cx v11 typ e1.
    body_exprs_ok cx [e1] ==>
    !tops ctx func cenv env ty st.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (TypeBuiltin v11 Convert typ [e1]) st /\
      (?a f cargs d. e1 = Call a (IntCall f) cargs d) /\
      lowered_value_type cenv e1 <> expr_type e1 ==>
      expr_sim ctx func cenv cx ty (TypeBuiltin v11 Convert typ [e1]) st /\
      expr_vv_sim ctx func cenv cx ty (TypeBuiltin v11 Convert typ [e1]) st
Proof
  cheat
QED

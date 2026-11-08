(*
 * Seam of bodyPtrTypeBuiltins: convert(e, T) for a single operand, outside
 * the signed bytestring case (bodyPtrTypeBuiltinsResidual) and the widened
 * internal-call operand (bodyPtrTypeBuiltinsConvertWidened).
 *
 * TOP-LEVEL:
 *   convert_unwidened_ptr
 *)
Theory bodyPtrTypeBuiltinsSeamConvert
Ancestors
  bodyPtrTypeBuiltinsCastExecution bodyPtrTypeBuiltinsCastSemantic
  bodyPtrTypeBuiltinsIntegerBytesRun bodyPtrTypeBuiltinsIntegerSemantic
  bodyPtrTypeBuiltinsLoweredRepresentation bodyPtrTypeBuiltinsMarkedBind
  bodyPtrTypeBuiltinsMemoryInterface bodyPtrTypeBuiltinsScalarSemantic
  bodyPtrTypeBuiltinsUintCounted
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

(* The lowering is the Convert branch of compile_type_builtin_dispatch_body
   (lower the operand, then a scalar transfer, a clamp, or a bytestring
   read/widening copy, by the source and target types); it returns a
   StackValue, so expr_vv_sim_ptr
   follows from expr_sim_ptr by expr_vv_sim_ptr_stack.  S1's proof of the
   case is in the exprSimConvert theories.  Outside the widened
   internal-call case, post_value_type cenv e1 = expr_type e1, so the
   operand's post describes its value at its own type.  The previous
   attempt proved this case on an older posts interface; its helpers
   (the Convert, Widen and Memory theories under alan-ref/typebuiltin-lane)
   stopped building here at widen_copy_actual_post, whose
   conclusion now needs post_value_type cenv e = expr_type e (its one use
   has a bytestring e, where that holds); the rest is untested on this
   base. *)
Theorem convert_unwidened_ptr:
  !cx v11 typ e1.
    body_exprs_ptr_ok cx [e1] ==>
    !d PG tops ctx func cenv env ty st.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (TypeBuiltin v11 Convert typ [e1]) st /\
      ~(is_bytestring_type (expr_type e1) /\
        ((?n. typ = BaseT (IntT n)) \/ typ = BaseT DecimalT)) /\
      ~((?a f cargs drv. e1 = Call a (IntCall f) cargs drv) /\
        lowered_value_type cenv e1 <> expr_type e1) ==>
      expr_sim_ptr d ctx PG func cenv cx ty (TypeBuiltin v11 Convert typ [e1]) st /\
      expr_vv_sim_ptr d ctx PG func cenv cx ty (TypeBuiltin v11 Convert typ [e1]) st
Proof
  cheat
QED

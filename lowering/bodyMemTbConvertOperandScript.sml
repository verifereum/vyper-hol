(* Singleton operand access for the plain convert case. *)
Theory bodyMemTbConvertOperand
Ancestors bodyMemoryPreds exprSimConvert vyperState vyperContext

Theorem convert_mem_operand_access:
  (!s'' x t.
     type_check (type_builtin_args_length_ok Convert (LENGTH es))
       "TypeBuiltin args" s'' = (INL x,t) ==>
     body_exprs_mem_ok cx es) /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst es) st /\
  ~(?e1 a f args d. es = [e1] /\ e1 = Call a (IntCall f) args d /\
      lowered_value_type cenv e1 <> expr_type e1) ==>
  ?e1. es = [e1] /\ ann = dst /\ valid_conversion (expr_type e1) dst /\
       expr_body_pre cenv cx env e1 st /\ body_expr_mem_ok cx e1 /\
       (!a f args d. e1 = Call a (IntCall f) args d ==>
         lowered_value_type cenv e1 = expr_type e1)
Proof
  strip_tac >> drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  `body_exprs_mem_ok cx [e1]` by
    (first_x_assum irule >>
     simp[type_check_def, assert_def, type_builtin_args_length_ok_def]) >>
  gvs[body_exprs_mem_ok_def]
QED

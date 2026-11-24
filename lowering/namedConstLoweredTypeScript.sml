Theory namedConstLoweredType
Ancestors
  exprLowering vyperTypeSystem vyperAST

(* A NamedConst wrapper preserves the physical layout of its fresh value,
   including the actual payload length of a bytelike literal. *)
Theorem lowered_value_type_named_const:
  !env ty e cenv. well_typed_expr env (Builtin ty NamedConst [e]) ==>
    lowered_value_type cenv (Builtin ty NamedConst [e]) = lowered_value_type cenv e
Proof
  simp[well_typed_expr_def, well_typed_builtin_app_def, builtin_operands_ok_def] >>
  rpt strip_tac >>
  Cases_on `e` >> gvs[named_const_operand_def, expr_type_def]
  >~ [`Literal ann lit`] >-
    (Cases_on `ann` >> simp[oneline lowered_value_type_def, expr_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> simp[])
  >~ [`Builtin ann NamedConst [Builtin ann bi args]`] >-
    (Cases_on `bi` >> gvs[named_const_operand_def] >>
     Cases_on `ann` >> simp[oneline lowered_value_type_def, expr_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> simp[]) >>
  rename1 `Builtin ann NamedConst [TypeBuiltin ann bi rt args]` >>
  Cases_on `bi` >> Cases_on `args` >> gvs[named_const_operand_def] >>
  Cases_on `ann` >> simp[oneline lowered_value_type_def, expr_type_def] >>
  rename1 `_ = BaseT bt` >> Cases_on `bt` >> simp[] >>
  rename1 `_ = BaseT (BytesT sz)` >> Cases_on `sz` >> simp[]
QED

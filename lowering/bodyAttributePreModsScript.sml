Theory bodyAttributePreMods
Ancestors
  exprSimHypsDefs supportedExprTraverse vyperTypeSystem vyperTypeCallGraph
  allocLimits

Theorem attribute_pre_child_mods:
  !mods cenv cx env es v9 e id.
    expr_body_pre_mods mods cenv cx env (Attribute v9 e id) es ==>
    expr_body_pre_mods mods cenv cx env e es
Proof
  simp[expr_body_pre_mods_def, Once well_typed_expr_def,
       byte_widths_expr_def, alloc_limits_expr_def, int_calls_expr_def,
       expr_has_evm_run_thm, supported_expr_exists_def] >>
  metis_tac[]
QED

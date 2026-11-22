Theory exprBodyPreTypingProps
Ancestors
  exprSimHypsDefs vyperTypeExprSoundness vyperTypeSystem
  vyperTypeInvariants

Theorem expr_body_pre_mods_runtime_typing:
  expr_body_pre_mods mods cenv cx env e es ==>
  runtime_consistent env cx es /\ well_typed_expr env e /\
  functions_well_typed cx
Proof
  simp[expr_body_pre_mods_def, expr_sim_inv_mods_def, runtime_consistent_def]
QED

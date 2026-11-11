Theory bodyPtrStructLitTypedShape
Ancestors loweringShapeProps loweringShapeRules loweringShapeDefs context
  compileEnv venomInst unitShapeDefs stackPlanTypes

Theorem structlit_typed_store_unequal_shape:
  dt <> st ==>
  shape_step internal compiler_label
    (\s. plain_operand s dst /\ plain_operand s src)
    (compile_store_memory_typed ce dst dt src st) (\u s. T)
Proof
  strip_tac >> MATCH_ACCEPT_TAC (cj 1 compile_typed_copy_shape)
QED

(* Semantic annotation resources for the reason literal shortcut. *)
Theory reasonLiteralPostPtr
Ancestors reasonLiteralBufferPtr reasonMemorySuccessPtr reasonResourcesPtr
  exprSimHyps exprSimHypsDefs vyperTypeSystem allocLimits vyperAST
  vyperValue bodyPtrDefs

Theorem reason_literal_source_bounds:
  expr_body_pre cenv cx env
    (Literal (BaseT (StringT ml)) (StringL str)) es ==>
  LENGTH str <= ml /\ type_alloc_ok cenv (BaseT (StringT ml)) /\
  64 + type_memory_bytes cenv (BaseT (StringT ml)) < dimword (:256)
Proof
  strip_tac >>
  `LENGTH str <= ml /\ type_alloc_ok cenv (BaseT (StringT ml))` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_literal_def,
        alloc_limits_expr_def] >>
  drule reason_encoder_allocation_limit >> simp[]
QED

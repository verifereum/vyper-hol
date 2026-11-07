Theory bodyPtrPopExprBoundary
Ancestors bodyPtrPopCompileDomain bodyPtrPopBaseExprBoundary
  bodyPtrPopFiniteProducerBoundary
  bodyPtrPopPlaceBoundary bodyPtrPopTraversalBoundary bodyPtrPopCallBoundary
  bodyPtrPopIfExpBoundary bodyPtrPopCompilerBoundary bodyPtrPopMaterialization
  bodyPtrPopAllocationBoundary exprLowering supportedExprs vyperAST list pair

Theorem pop_domain_ifexp_body_boundary:
  (!cenv aty e s v t. pop_compile_domain tops e /\ pop_comp_boundary s /\
    cfn cenv aty e s = (v,t) ==> pop_comp_boundary t) /\
  pop_compile_domain tops (IfExp rt cond a b) /\ pop_comp_boundary sa /\
  compile_expr_body cfn bfn tfn cenv ty (IfExp rt cond a b) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  rpt strip_tac >> drule pop_domain_ifexp_children >> strip_tac >>
  drule_at (Pat `compile_expr_body _ _ _ _ _ _ _ = _`) pop_ifexp_body_boundary >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  gvs[] >> qpat_x_assum `!cenv aty e s v t. _` drule_all >> simp[]
QED

Theorem pop_domain_subscript_body_boundary:
  (!cenv aty e s v t. pop_compile_domain tops e /\ pop_comp_boundary s /\
    cfn cenv aty e s = (v,t) ==> pop_comp_boundary t) /\
  pop_compile_domain tops (Subscript rt base_e idx_e) /\ pop_comp_boundary sa /\
  compile_expr_body cfn bfn tfn cenv ty (Subscript rt base_e idx_e) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_expr_body_def, expr_type_def] >> rpt strip_tac >>
  drule pop_domain_subscript_children >> strip_tac >>
  drule_at (Pat `compile_subscript _ _ _ _ _ _ _ = _`) pop_compile_subscript_boundary >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  gvs[] >> qpat_x_assum `!cenv aty e s v t. _` drule_all >> simp[]
QED

Theorem pop_domain_attribute_body_boundary:
  (!cenv aty e s v t. pop_compile_domain tops e /\ pop_comp_boundary s /\
    cfn cenv aty e s = (v,t) ==> pop_comp_boundary t) /\
  pop_compile_domain tops (Attribute rt base_e fld) /\ pop_comp_boundary sa /\
  compile_expr_body cfn bfn tfn cenv ty (Attribute rt base_e fld) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_expr_body_def, expr_type_def] >> rpt strip_tac >>
  drule pop_domain_attribute_child >> strip_tac >>
  drule_at (Pat `compile_attribute _ _ _ _ _ _ _ = _`) pop_compile_attribute_boundary >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  gvs[] >> qpat_x_assum `!cenv aty e s v t. _` drule_all >> simp[]
QED

Theorem pop_domain_struct_body_boundary:
  (!cenv aty e s v t. pop_compile_domain tops e /\ pop_comp_boundary s /\
    cfn cenv aty e s = (v,t) ==> pop_comp_boundary t) /\
  pop_compile_domain tops (StructLit rt id fields) /\ pop_comp_boundary sa /\
  compile_expr_body cfn bfn tfn cenv ty (StructLit rt id fields) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_expr_body_def, expr_type_def] >> rpt strip_tac >>
  drule pop_domain_struct_fields >> strip_tac >>
  pairarg_tac >> gvs[IgnAsm `!cenv aty e s v t. _`] >>
  drule_all pop_compile_alloc_buffer_boundary >> strip_tac >>
  pairarg_tac >> gvs[IgnAsm `!cenv aty e s v t. _`] >>
  drule_at (Pat `compile_struct_lit _ _ _ _ _ _ _ = _`) pop_compile_struct_lit_boundary >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  `pop_compile_domain tops e` by
    (drule pop_domain_struct_child >> disch_then irule >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `!cenv aty e s v t. _` drule_all >> simp[]
QED


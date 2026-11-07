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


Theorem pop_builtin_body_handoff:
  compile_expr_body cfn bfn tfn cenv ty (Builtin rt bi args) sa =
    bfn cenv rt ty bi args sa \/
  (?at a bt b mt m. bi = AddMod /\ args = [Name at a; Name bt b; Name mt m] /\
    compile_expr_body cfn bfn tfn cenv ty (Builtin rt bi args) sa =
      compile_addmod_names cenv rt at a bt b mt m sa) \/
  (?at a bt b mt m. bi = MulMod /\ args = [Name at a; Name bt b; Name mt m] /\
    compile_expr_body cfn bfn tfn cenv ty (Builtin rt bi args) sa =
      compile_mulmod_names cenv rt at a bt b mt m sa) \/
  (?at a bt b. bi = PowMod256 /\ args = [Name at a; Name bt b] /\
    compile_expr_body cfn bfn tfn cenv ty (Builtin rt bi args) sa =
      compile_powmod256_names cenv rt at a bt b sa)
Proof
  Cases_on `args` >> simp[compile_expr_body_def, expr_type_def] >>
  rename1 `bfn cenv rt ty bi (a::rest)` >>
  Cases_on `a` >> simp[compile_expr_body_def, expr_type_def] >>
  Cases_on `rest` >> simp[compile_expr_body_def, expr_type_def] >>
  rename1 `bfn cenv rt ty bi (_::b::rest)` >>
  Cases_on `b` >> simp[compile_expr_body_def, expr_type_def] >>
  Cases_on `rest`
  >- (Cases_on `bi` >> simp[compile_expr_body_def, expr_type_def]) >>
  simp[compile_expr_body_def, expr_type_def] >>
  rename1 `bfn cenv rt ty bi (_::_::c::rest)` >>
  Cases_on `c` >> simp[compile_expr_body_def, expr_type_def] >>
  Cases_on `rest` >> simp[compile_expr_body_def, expr_type_def] >>
  Cases_on `bi` >> simp[compile_expr_body_def, expr_type_def]
QED

Theorem pop_domain_builtin_body_boundary:
  (!cenv rt ty bi args s v t.
    supported_builtin_form tops rt bi args /\
    EVERY (supported_pure_expr tops) args /\ pop_comp_boundary s /\
    bfn cenv rt ty bi args s = (v,t) ==> pop_comp_boundary t) /\
  pop_compile_domain tops (Builtin rt bi args) /\ pop_comp_boundary sa /\
  compile_expr_body cfn bfn tfn cenv ty (Builtin rt bi args) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  rpt strip_tac >> drule pop_domain_builtin_form >> strip_tac >>
  mp_tac pop_builtin_body_handoff >> strip_tac >> gvs[]
  >- (qpat_x_assum `!cenv rt ty bi args s v t. _` drule_all >> simp[]) 
  >- (drule_all pop_compile_addmod_names_boundary >> simp[])
  >- (drule_all pop_compile_mulmod_names_boundary >> simp[]) >>
  drule_all pop_compile_powmod256_names_boundary >> simp[]
QED

Theorem pop_domain_type_builtin_body_boundary:
  (!cenv vt ty tb rt args s v t.
    supported_type_builtin_form tops vt tb rt args /\
    EVERY (supported_pure_expr tops) args /\ pop_comp_boundary s /\
    tfn cenv vt ty tb rt args s = (v,t) ==> pop_comp_boundary t) /\
  pop_compile_domain tops (TypeBuiltin vt tb rt args) /\ pop_comp_boundary sa /\
  compile_expr_body cfn bfn tfn cenv ty (TypeBuiltin vt tb rt args) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_expr_body_def, expr_type_def] >> rpt strip_tac >>
  drule pop_domain_type_builtin_form >> strip_tac >>
  qpat_x_assum `!cenv vt ty tb rt args s v t. _` drule_all >> simp[]
QED

Theorem pop_domain_call_body_boundary:
  (!cenv aty e s v t. pop_compile_domain tops e /\ pop_comp_boundary s /\
    cfn cenv aty e s = (v,t) ==> pop_comp_boundary t) /\
  pop_compile_domain tops (Call rt target args default_ret) /\ pop_comp_boundary sa /\
  compile_expr_body cfn bfn tfn cenv ty (Call rt target args default_ret) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_expr_body_def, expr_type_def] >> rpt strip_tac >>
  drule_all pop_compile_call_boundary >> simp[]
QED

Theorem pop_domain_pop_body_boundary:
  pop_compile_domain tops (Pop rt target) /\ pop_comp_boundary sa /\
  compile_expr_body cfn bfn tfn cenv ty (Pop rt target) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  rpt strip_tac >> drule pop_domain_pop_target >> strip_tac >> gvs[] >>
  drule_all pop_toplevel_pop_body_boundary >> simp[]
QED

Theorem pop_expr_open_boundary:
  !cfn bfn tfn.
  (!cenv ty e sa r sb. pop_compile_domain tops e /\ pop_comp_boundary sa /\
    cfn cenv ty e sa = (r,sb) ==> pop_comp_boundary sb) /\
  (!cenv rt ty bi args sa r sb. supported_builtin_form tops rt bi args /\
    EVERY (supported_pure_expr tops) args /\ pop_comp_boundary sa /\
    bfn cenv rt ty bi args sa = (r,sb) ==> pop_comp_boundary sb) /\
  (!cenv vt ty tb rt args sa r sb. supported_type_builtin_form tops vt tb rt args /\
    EVERY (supported_pure_expr tops) args /\ pop_comp_boundary sa /\
    tfn cenv vt ty tb rt args sa = (r,sb) ==> pop_comp_boundary sb) ==>
  !cenv ty e sa r sb. pop_compile_domain tops e /\ pop_comp_boundary sa /\
    compile_expr_body cfn bfn tfn cenv ty e sa = (r,sb) ==> pop_comp_boundary sb
Proof
  rpt strip_tac >> Cases_on `e` >>
  FIRST_PROVE
    [drule_all pop_literal_body_boundary >> simp[],
     drule_all pop_name_body_boundary >> simp[],
     drule_all pop_toplevel_name_body_boundary >> simp[],
     drule_all pop_domain_ifexp_body_boundary >> simp[],
     drule_all pop_domain_subscript_body_boundary >> simp[],
     drule_all pop_domain_attribute_body_boundary >> simp[],
     drule_all pop_domain_struct_body_boundary >> simp[],
     drule_all pop_domain_builtin_body_boundary >> simp[],
     drule_all pop_domain_type_builtin_body_boundary >> simp[],
     drule_all pop_domain_call_body_boundary >> simp[],
     drule_all pop_domain_pop_body_boundary >> simp[],
     gvs[compile_expr_body_def, expr_type_def]]
QED

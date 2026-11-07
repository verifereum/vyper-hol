Theory bodyPtrPopMathIntegration
Ancestors bodyPtrPopSliceIntegration bodyPtrPopSmallMathBoundary
  bodyPtrPopMaterialization
  exprLowering exprCallBounds supportedExprForms supportedExprs
  compileEnv emitHelper list

Theorem pop_expr_child_typed_boundary:
  (!s v t. expr_size a < bound /\ pop_comp_boundary s /\
    cfn (cenv:compile_env) (aty:type) a s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\
  expr_child_callback bound cfn cenv aty a sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `expr_size a < bound` >> simp[expr_child_callback_def] >>
  rpt strip_tac
  >- (metis_tac[]) >>
  drule_all pop_invalid_expr_boundary >> simp[]
QED

Theorem pop_single_math_dispatch_boundary:
  (bi = Neg \/ bi = Abs) /\
  (!a aty s v t. MEM a [e] /\ pop_comp_boundary s /\
    cfn cenv aty a s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\
  compile_builtin_dispatch_body cfn cenv ret_ty ty bi [e] sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  strip_tac >> gvs[] >>
  gvs[compile_builtin_dispatch_body_def] >> pairarg_tac >> gvs[] >>
  `pop_comp_boundary st1` by
    (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
     disch_then irule >> simp[] >> rpt strip_tac >>
     metis_tac[]) >>
  Cases_on `compile_neg v (expr_type e) st1` >>
  Cases_on `compile_builtin_abs v st1` >> gvs[as_stack_val_def] >>
  metis_tac[pop_compile_neg_boundary, pop_compile_builtin_abs_boundary]
QED

Theorem pop_triple_math_dispatch_boundary:
  (bi = AddMod \/ bi = MulMod) /\
  (!a aty s v t. MEM a [a1;a2;a3] /\ pop_comp_boundary s /\
    cfn cenv aty a s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\
  compile_builtin_dispatch_body cfn cenv ret_ty ty bi [a1;a2;a3] sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  strip_tac >> gvs[] >>
  gvs[compile_builtin_dispatch_body_def] >> pairarg_tac >> gvs[] >>
  `pop_comp_boundary st1` by
    (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
     disch_then irule >> simp[] >> rpt strip_tac >>
     metis_tac[]) >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st2` by
    (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
     disch_then irule >> simp[] >> rpt strip_tac >>
     metis_tac[]) >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st3` by
    (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
     disch_then irule >> simp[] >> rpt strip_tac >>
     metis_tac[]) >>
  Cases_on `compile_addmod va vb vc st3` >>
  Cases_on `compile_mulmod va vb vc st3` >> gvs[as_stack_val_def] >>
  metis_tac[pop_compile_addmod_boundary, pop_compile_mulmod_boundary]
QED

Theorem pop_single_math_supported_shape:
  (bi = Neg \/ bi = Abs) /\ supported_builtin_form tops ret_ty bi args ==>
  ?a. args = [a]
Proof
  strip_tac >> gvs[] >> Cases_on `args` >>
  gvs[supported_builtin_form_def] >> Cases_on `t` >> gvs[]
QED

Theorem pop_triple_math_supported_shape:
  (bi = AddMod \/ bi = MulMod) /\ supported_builtin_form tops ret_ty bi args ==>
  ?a b c. args = [a;b;c]
Proof
  strip_tac >> gvs[] >> Cases_on `args` >>
  gvs[supported_builtin_form_def] >> Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >> Cases_on `t` >> gvs[]
QED

Theorem pop_math_dispatch_boundary:
  (bi = Neg \/ bi = Abs \/ bi = AddMod \/ bi = MulMod) /\
  supported_builtin_form tops ret_ty bi args /\
  (!a aty s v t. MEM a args /\ pop_comp_boundary s /\
    cfn cenv aty a s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\
  compile_builtin_dispatch_body cfn cenv ret_ty ty bi args sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `bi = Neg \/ bi = Abs`
  >- (drule_all pop_single_math_supported_shape >> strip_tac >> gvs[] >>
      drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)
        pop_single_math_dispatch_boundary >> disch_then irule >> simp[] >>
      metis_tac[]) >>
  `bi = AddMod \/ bi = MulMod` by metis_tac[] >>
  drule_at (Pat `supported_builtin_form _ _ _ _`)
    pop_triple_math_supported_shape >> simp[] >> strip_tac >> gvs[] >>
  drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)
    pop_triple_math_dispatch_boundary >> disch_then irule >> simp[] >>
  metis_tac[]
QED

Theorem pop_supported_math_dispatch_boundary:
  (bi = Neg \/ bi = Abs \/ bi = AddMod \/ bi = MulMod) /\
  supported_builtin_form tops ret_ty bi args /\
  EVERY (supported_pure_expr tops) args /\
  (!a aty s v t. supported_pure_expr tops a /\ expr_size a < bound /\
    pop_comp_boundary s /\ cfn cenv aty a s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\
  compile_builtin_dispatch_body (expr_child_callback bound cfn)
    cenv ret_ty ty bi args sa = (r,sb) ==> pop_comp_boundary sb
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)
    pop_math_dispatch_boundary >> disch_then irule >>
  simp[Excl "expr_child_callback_def"] >>
  reverse conj_tac >- (qexists_tac `tops` >> simp[]) >> rpt strip_tac >>
  irule pop_expr_child_typed_boundary >>
  goal_assum (drule_at Any) >> simp[Excl "expr_child_callback_def"] >>
  rpt strip_tac >> fs[EVERY_MEM] >> metis_tac[]
QED

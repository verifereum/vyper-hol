Theory bodyPtrPopBaseExprBoundary
Ancestors bodyPtrPopSupportedBoundary bodyPtrPopFiniteProducerBoundary
  bodyPtrPopMaterialization exprLowering compileEnv finite_map

Theorem pop_literal_body_boundary:
  pop_comp_boundary sa /\
  compile_expr_body cfn bfn tfn cenv ty (Literal rt lit) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_expr_body_def] >> strip_tac >>
  drule_all pop_compile_literal_vv_boundary >> simp[]
QED

Theorem pop_name_body_boundary:
  pop_comp_boundary sa /\
  compile_expr_body cfn bfn tfn cenv ty (Name rt id) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_expr_body_def] >> strip_tac >>
  drule_all pop_compile_name_vv_boundary >> simp[]
QED

Theorem pop_toplevel_name_body_boundary:
  pop_comp_boundary sa /\
  compile_expr_body cfn bfn tfn cenv ty (TopLevelName rt id) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_expr_body_def] >> strip_tac >>
  Cases_on `FLOOKUP cenv.ce_module_vars id` >> gvs[]
  >- (pairarg_tac >> gvs[] >> drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[]) >>
  Cases_on `x` >> gvs[] >> pairarg_tac >> gvs[] >>
  drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[]
QED

Theorem pop_addmod_names_body_boundary:
  pop_comp_boundary sa /\
  compile_expr_body cfn bfn tfn cenv ty
    (Builtin rt AddMod [Name aty a; Name bty b; Name mty m]) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_expr_body_def] >> strip_tac >>
  drule_all pop_compile_addmod_names_boundary >> simp[]
QED

Theorem pop_mulmod_names_body_boundary:
  pop_comp_boundary sa /\
  compile_expr_body cfn bfn tfn cenv ty
    (Builtin rt MulMod [Name aty a; Name bty b; Name mty m]) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_expr_body_def] >> strip_tac >>
  drule_all pop_compile_mulmod_names_boundary >> simp[]
QED

Theorem pop_powmod256_names_body_boundary:
  pop_comp_boundary sa /\
  compile_expr_body cfn bfn tfn cenv ty
    (Builtin rt PowMod256 [Name aty a; Name bty b]) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_expr_body_def] >> strip_tac >>
  drule_all pop_compile_powmod256_names_boundary >> simp[]
QED

Theorem pop_toplevel_pop_body_boundary:
  pop_comp_boundary sa /\
  compile_expr_body cfn bfn tfn cenv ty
    (Pop rt (TopLevelNameTarget id)) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_expr_body_def] >> strip_tac >>
  pairarg_tac >> gvs[] >>
  drule pop_toplevel_target_literal >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  drule_all pop_literal_scaled_locations_boundary >> simp[]
QED

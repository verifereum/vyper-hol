Theory bodyPtrPopInternalParamsBoundary
Ancestors moduleLowering bodyPtrPopCompilerBoundary bodyPtrPopArithmeticBoundary
  bodyPtrPopAllocationBoundary compileEnv finite_map list

Theorem pop_internal_param_decls_boundary:
  !params idx sa r sb.
    pop_comp_boundary sa /\ compile_internal_param_decls params idx sa = (r,sb) ==>
    pop_comp_boundary sb
Proof
  Induct >> simp[compile_internal_param_decls_def, comp_return_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_internal_param_decls_def] >> strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE [drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[],
    first_x_assum drule_all >> simp[], gvs[comp_return_def]]
QED

Theorem pop_materialize_internal_params_boundary:
  !params ce sa r sb.
    pop_comp_boundary sa /\ materialize_internal_params ce params sa = (r,sb) ==>
    pop_comp_boundary sb
Proof
  Induct >> simp[materialize_internal_params_def, comp_return_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  Cases_on `h1` >> simp[materialize_internal_params_def, comp_ignore_bind_def] >>
  rpt strip_tac >> FIRST_PROVE
    [first_x_assum drule_all >> simp[],
     (Cases_on `FLOOKUP ce.ce_vars h0` >> gvs[]
      >- (first_x_assum drule_all >> simp[]) >>
      Cases_on `x` >> gvs[] >>
      rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
           disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
      FIRST_PROVE
        [first_x_assum drule_all >> simp[],
         drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[],
         drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[]])]
QED

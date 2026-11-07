Theory bodyPtrPopArgumentsBoundary
Ancestors moduleLowering bodyPtrPopCompilerBoundary bodyPtrPopArithmeticBoundary
  bodyPtrPopAllocationBoundary bodyPtrPopAbiDecodeBoundary
  bodyPtrPopAbiDecodePrimitiveBoundary compileEnv finite_map list

Theorem pop_decode_args_boundary:
  !args ce offset lop hi base sa r sb.
    lop <> ASSERT /\ pop_comp_boundary sa /\
    compile_decode_args ce args offset lop hi base sa = (r,sb) ==> pop_comp_boundary sb
Proof
  Induct >> simp[compile_decode_args_def, comp_return_def] >>
  rpt gen_tac >> PairCases_on `h` >> Cases_on `h1` >> Cases_on `h2` >>
  Cases_on `FLOOKUP ce.ce_vars h0` >>
  simp[compile_decode_args_def, comp_ignore_bind_def] >>
  TRY (rename1 `FLOOKUP _ _ = SOME loc` >>
       Cases_on `var_location_decode_operand loc` >> simp[]) >>
  rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [first_x_assum drule_all >> simp[],
     drule_all pop_compile_abi_decode_to_buf_boundary >> simp[],
     drule_all pop_compile_abi_clamp_basetype_boundary >> simp[],
     drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[],
     drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[],
     gvs[comp_return_def]]
QED

Theorem pop_register_positional_args_boundary:
  !args ce offset sa r sb.
    pop_comp_boundary sa /\
    compile_register_positional_args ce args offset sa = (r,sb) ==> pop_comp_boundary sb
Proof
  Induct >> simp[compile_register_positional_args_def, comp_return_def] >>
  rpt gen_tac >> PairCases_on `h` >> Cases_on `FLOOKUP ce.ce_vars h0` >>
  simp[compile_register_positional_args_def, comp_ignore_bind_def] >>
  TRY (rename1 `FLOOKUP _ _ = SOME loc` >>
       Cases_on `var_location_memory_size loc` >> simp[]) >>
  rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [first_x_assum drule_all >> simp[],
     drule_all pop_compile_alloc_buffer_boundary >> simp[],
     drule_at (Pat `compile_decode_args _ _ _ _ _ _ _ = _`) pop_decode_args_boundary >>
       disch_then irule >> simp[],
     gvs[comp_return_def]]
QED

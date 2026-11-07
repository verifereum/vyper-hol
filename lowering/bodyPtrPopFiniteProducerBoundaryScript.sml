Theory bodyPtrPopFiniteProducerBoundary
Ancestors bodyPtrPopMaterialization bodyPtrPopSmallMathBoundary
  bodyPtrPopArithmeticBoundary
  bodyPtrPopAllocationBoundary bodyPtrPopCompilerBoundary
  exprLowering builtinMath compileEnv emitHelper list finite_map

Theorem pop_compile_name_vv_boundary:
  pop_comp_boundary sa /\ compile_name_vv cenv ty id sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `FLOOKUP cenv.ce_vars id` >> simp[compile_name_vv_def]
  >- (simp[comp_ignore_bind_def] >> rpt strip_tac >>
      drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
      disch_then irule >> simp[] >> conj_tac
      >- (rpt strip_tac >> drule_at (Pat `emit_inst _ _ _ _ = _`)
            pop_emit_inst_boundary >> simp[]) >>
      rpt strip_tac >> gvs[comp_return_def]) >>
  Cases_on `x` >> simp[compile_name_vv_def, comp_return_def] >> rpt strip_tac >>
  gvs[comp_ignore_bind_def] >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary,
         drule_at (Pat `comp_return _ _ = _`) pop_comp_boundary_return] >> simp[]
QED

Theorem pop_compile_store_byte_chunks_boundary:
  !dp bs off sa r sb.
  pop_comp_boundary sa /\ compile_store_byte_chunks dp bs off sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  recInduct compile_store_byte_chunks_ind >> rpt strip_tac >>
  gvs[compile_store_byte_chunks_def, comp_ignore_bind_def, comp_return_def] >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_at (Pat `emit_op _ _ _ = _`)
        pop_emit_op_boundary >> simp[]) >>
  rpt strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_at (Pat `emit_void _ _ _ = _`)
        pop_emit_void_boundary >> simp[]) >>
  rpt strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem pop_compile_bytelike_literal_boundary:
  pop_comp_boundary sa /\ compile_bytelike_literal bs n sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_bytelike_literal_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_at (Pat `compile_alloc_buffer _ _ = _`) pop_compile_alloc_buffer_boundary,
         drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary,
         drule_at (Pat `compile_store_byte_chunks _ _ _ _ = _`)
           pop_compile_store_byte_chunks_boundary,
         drule_at (Pat `comp_return _ _ = _`) pop_comp_boundary_return] >> simp[]
QED

Theorem pop_compile_literal_vv_boundary:
  pop_comp_boundary sa /\ compile_literal_vv ty lit sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `lit` >> simp[compile_literal_vv_def, comp_return_def] >> rpt strip_tac >>
  gvs[]
  >- (Cases_on `b` >> gvs[compile_literal_vv_def, comp_return_def])
  >- (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
      disch_then irule >> simp[] >> conj_tac
      >- (rpt strip_tac >> gvs[comp_return_def]) >>
      rpt strip_tac >> drule_at (Pat `compile_bytelike_literal _ _ _ = _`)
        pop_compile_bytelike_literal_boundary >> simp[]) >>
  Cases_on `ty` >> gvs[comp_return_def] >>
  Cases_on `b` >> gvs[comp_return_def] >>
  Cases_on `b'` >> gvs[comp_return_def] >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[comp_return_def]) >>
  rpt strip_tac >> drule_at (Pat `compile_bytelike_literal _ _ _ = _`)
    pop_compile_bytelike_literal_boundary >> simp[]
QED

Theorem pop_compile_pow_mod256_boundary:
  pop_comp_boundary sa /\ compile_pow_mod256 a b sa = (r,sb) ==> pop_comp_boundary sb
Proof
  simp[compile_pow_mod256_def] >> rpt strip_tac >>
  drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]
QED

Theorem pop_compile_addmod_names_boundary:
  pop_comp_boundary sa /\ compile_addmod_names cenv rt aty a bty b mty m sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_addmod_names_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_all pop_compile_name_vv_boundary >> strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_all pop_unwrap_value_boundary >> strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_all pop_compile_name_vv_boundary >> strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_all pop_unwrap_value_boundary >> strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_all pop_compile_name_vv_boundary >> strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_all pop_unwrap_value_boundary >> strip_tac >>
  Cases_on `compile_addmod va vb vm st6` >> gvs[as_stack_val_def] >>
  drule_all pop_compile_addmod_boundary >> simp[]
QED

Theorem pop_compile_mulmod_names_boundary:
  pop_comp_boundary sa /\ compile_mulmod_names cenv rt aty a bty b mty m sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_mulmod_names_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_all pop_compile_name_vv_boundary >> strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_all pop_unwrap_value_boundary >> strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_all pop_compile_name_vv_boundary >> strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_all pop_unwrap_value_boundary >> strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_all pop_compile_name_vv_boundary >> strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_all pop_unwrap_value_boundary >> strip_tac >>
  Cases_on `compile_mulmod va vb vm st6` >> gvs[as_stack_val_def] >>
  drule_all pop_compile_mulmod_boundary >> simp[]
QED

Theorem pop_compile_powmod256_names_boundary:
  pop_comp_boundary sa /\ compile_powmod256_names cenv rt aty a bty b sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_powmod256_names_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_all pop_compile_name_vv_boundary >> strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_all pop_unwrap_value_boundary >> strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_all pop_compile_name_vv_boundary >> strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_all pop_unwrap_value_boundary >> strip_tac >>
  Cases_on `compile_pow_mod256 va vb st4` >> gvs[as_stack_val_def] >>
  drule_all pop_compile_pow_mod256_boundary >> simp[]
QED

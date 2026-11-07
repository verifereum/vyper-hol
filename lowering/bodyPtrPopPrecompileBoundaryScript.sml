Theory bodyPtrPopPrecompileBoundary
Ancestors bodyPtrPopClampBoundary bodyPtrPopCompilerBoundary
  bodyPtrPopBoundaryContract bodyPtrPopGuardedWindow
  bodyPtrPopAllocationBoundary bodyPtrPopArithmeticBoundary
  builtinMisc compileEnv emitHelper venomInst list
Libs monadsyntax

Theorem pop_staticcall_guard_template:
  MAP (\i. i.inst_opcode) t = [STATICCALL;ASSERT] /\
  pop_boundary_clean p ==> pop_boundary_clean (p ++ t)
Proof
  simp[MAP_EQ_CONS] >> rpt strip_tac >> gvs[] >>
  irule pop_boundary_append_no_sub >> simp[] >>
  simp[pop_guard4_def] >> rpt strip_tac >> gvs[mk_inst_def]
QED

Theorem pop_staticcall_guard_boundary:
  pop_comp_boundary sa /\
  (do success <- emit_op STATICCALL args; emit_void ASSERT [success] od) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_staticcall_guard_template >> simp[mk_inst_def]
QED

Theorem pop_staticcall_guard_then_boundary:
  pop_comp_boundary sa /\
  (!s x t. pop_comp_boundary s /\ k s = (x,t) ==> pop_comp_boundary t) /\
  (do success <- emit_op STATICCALL args;
      ignored <- emit_void ASSERT [success]; k od) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  CONV_TAC (ONCE_DEPTH_CONV (HO_REWR_CONV (GSYM comp_bind_assoc))) >>
  rpt strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[comp_bind_assoc] >>
      drule_at (Pat `comp_bind _ _ _ = _`) pop_staticcall_guard_boundary >> simp[]) >>
  rpt strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem pop_compile_ecrecover_boundary:
  pop_comp_boundary sa /\ compile_ecrecover hash v rop sop sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_ecrecover_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (FIRST [
    (drule_at (Pat `comp_bind _ _ _ = _`) pop_staticcall_guard_then_boundary >>
     disch_then irule >> simp[] >> rpt gen_tac >> strip_tac),
    (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
     disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac)]) >>
  FIRST [drule_all pop_compile_alloc_buffer_boundary,
         drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary,
         drule_all pop_comp_boundary_return] >> simp[]
QED

Theorem pop_compile_ecadd_points_boundary:
  pop_comp_boundary sa /\ compile_ecadd_points p1 p2 sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_ecadd_points_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (FIRST [
    (drule_at (Pat `comp_bind _ _ _ = _`) pop_staticcall_guard_then_boundary >>
     disch_then irule >> simp[] >> rpt gen_tac >> strip_tac),
    (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
     disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac)]) >>
  FIRST [drule_all pop_compile_alloc_buffer_boundary,
         drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary,
         drule_all pop_comp_boundary_return] >> simp[]
QED

Theorem pop_compile_ecmul_point_boundary:
  pop_comp_boundary sa /\ compile_ecmul_point p scalar sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_ecmul_point_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (FIRST [
    (drule_at (Pat `comp_bind _ _ _ = _`) pop_staticcall_guard_then_boundary >>
     disch_then irule >> simp[] >> rpt gen_tac >> strip_tac),
    (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
     disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac)]) >>
  FIRST [drule_all pop_compile_alloc_buffer_boundary,
         drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary,
         drule_all pop_comp_boundary_return] >> simp[]
QED

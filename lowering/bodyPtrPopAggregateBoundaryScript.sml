Theory bodyPtrPopAggregateBoundary
Ancestors bodyPtrPopMaterialization bodyPtrPopTypedCopyBoundary
  bodyPtrPopAllocationBoundary
  bodyPtrPopArithmeticBoundary bodyPtrPopCompilerBoundary
  exprLowering compileEnv emitHelper list

Theorem pop_compile_make_tuple_boundary:
  !args buf off sa r sb.
  (!a aty s v t. MEM a args /\ pop_comp_boundary s /\
    cfn cenv aty a s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\ compile_make_tuple cfn cenv args buf off sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Induct
  >- (simp[compile_make_tuple_def] >> rpt strip_tac >>
      drule_all pop_comp_boundary_return >> simp[]) >>
  simp[compile_make_tuple_def, comp_ignore_bind_def] >> rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!a aty s v t. _` (qspec_then `h` mp_tac) >>
      simp[] >> disch_then drule_all >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_at (Pat `emit_op _ _ _ = _`)
      pop_emit_op_boundary >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all pop_unwrap_value_boundary >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all pop_compile_store_memory_boundary >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!buf off sa r sb. _ /\ _ /\ compile_make_tuple _ _ _ _ _ _ = _ ==> _` irule >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!a aty s v t. _` (qspec_then `a` mp_tac) >>
      simp[] >> disch_then drule_all >> simp[]) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem pop_compile_make_array_elems_boundary:
  !args et sz hl buf idx sa r sb.
  (!a aty s v t. MEM a args /\ pop_comp_boundary s /\
    cfn cenv aty a s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\
  compile_make_array_elems cfn cenv args et sz hl buf idx sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Induct
  >- (simp[compile_make_array_elems_def] >> rpt strip_tac >>
      drule_all pop_comp_boundary_return >> simp[]) >>
  simp[compile_make_array_elems_def, comp_ignore_bind_def] >> rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!a aty s v t. _` (qspec_then `h` mp_tac) >>
      simp[] >> disch_then drule_all >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_at (Pat `emit_op _ _ _ = _`)
      pop_emit_op_boundary >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all pop_unwrap_value_boundary >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all pop_compile_store_memory_boundary >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!et sz hl buf idx sa r sb. _ /\ _ /\ compile_make_array_elems _ _ _ _ _ _ _ _ _ = _ ==> _` irule >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!a aty s v t. _` (qspec_then `a` mp_tac) >>
      simp[] >> disch_then drule_all >> simp[]) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem pop_compile_make_array_boundary:
  (!a aty s v t. MEM a args /\ pop_comp_boundary s /\
    cfn cenv aty a s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\
  compile_make_array cfn cenv args et sz hl buf sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_make_array_def, comp_ignore_bind_def] >> rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `hl` >> gvs[]
      >- (drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[]) >>
      drule_all pop_comp_boundary_return >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `compile_make_array_elems _ _ _ _ _ _ _ _ _ = _`)
    pop_compile_make_array_elems_boundary >> simp[] >>
  disch_then irule >> first_assum ACCEPT_TAC
QED

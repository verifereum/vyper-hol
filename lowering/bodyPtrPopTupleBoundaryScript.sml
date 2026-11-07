Theory bodyPtrPopTupleBoundary
Ancestors bodyPtrPopTargetBoundary bodyPtrPopAssignmentBoundary
  bodyPtrPopCompilerBoundary bodyPtrPopArithmeticBoundary bodyPtrPopMaterialization
  bodyPtrPopAllocationBoundary stmtLowering compileEnv exprLowering emitHelper
  supportedStmts list venomInst context

Theorem pop_compile_load_memory_boundary:
  pop_comp_boundary sa /\ compile_load_memory src prim sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `prim` >> simp[compile_load_memory_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >>
  drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]
QED

Theorem pop_compile_load_tuple_elements_boundary:
  !tys offset sa r sb. pop_comp_boundary sa /\
  compile_load_tuple_elements ce src tys offset sa = (r,sb) ==> pop_comp_boundary sb
Proof
  Induct_on `tys` >> simp[compile_load_tuple_elements_def]
  >- (rpt strip_tac >> gvs[comp_return_def]) >>
  rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[],
     first_x_assum drule_all >> simp[], gvs[comp_return_def]]
QED

Theorem pop_compile_tuple_load_all_boundary:
  !tys offset sa r sb. pop_comp_boundary sa /\
  compile_tuple_load_all ce src tys offset sa = (r,sb) ==> pop_comp_boundary sb
Proof
  Induct_on `tys` >> simp[compile_tuple_load_all_def]
  >- (rpt strip_tac >> gvs[comp_return_def]) >>
  rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[],
     drule_all pop_compile_load_memory_boundary >> simp[],
     first_x_assum drule_all >> simp[], gvs[comp_return_def]]
QED

Theorem pop_compile_tuple_store_all_boundary:
  !targets tys vals sa r sb.
  EVERY (\g. case g of BaseTarget bt => supported_target tops bindings bt
                       | TupleTarget _ => F) targets /\
  pop_comp_boundary sa /\
  compile_tuple_store_all ce tys targets vals sa = (r,sb) ==> pop_comp_boundary sb
Proof
  Induct_on `targets`
  >- (Cases_on `tys` >> Cases_on `vals` >>
      simp[compile_tuple_store_all_def, comp_return_def]) >>
  qx_gen_tac `target` >>
  Cases_on `target` >> Cases_on `tys` >> Cases_on `vals` >>
  simp[compile_tuple_store_all_def, comp_return_def, comp_ignore_bind_def] >>
  rpt strip_tac >> gvs[] >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [(drule_at (Pat `compile_get_target_ptr _ _ _ _ = _`) pop_compile_target_boundary >>
      disch_then irule >> simp[] >> qexistsl [`bindings`, `tops`] >> simp[]),
     first_x_assum drule_all >> simp[],
     (qpat_x_assum `(if guard then _ else _) _ = _` mp_tac >>
      rpt IF_CASES_TAC >> simp[] >> strip_tac >> FIRST_PROVE
        [drule_all pop_compile_store_at_loc_boundary >> simp[],
         drule_all pop_compile_assign_value_boundary >> simp[],
         drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[]]),
     gvs[comp_return_def]]
QED

Theorem pop_compile_tuple_unpack_boundary:
  EVERY (\g. case g of BaseTarget bt => supported_target tops bindings bt
                       | TupleTarget _ => F) targets /\
  pop_comp_boundary sa /\
  compile_tuple_unpack ce ty stage targets src sa = (r,sb) ==> pop_comp_boundary sb
Proof
  simp[compile_tuple_unpack_def, comp_ignore_bind_def] >>
  rpt IF_CASES_TAC >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[],
     drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[],
     drule_all pop_compile_alloc_buffer_boundary >> simp[],
     drule_all pop_compile_tuple_load_all_boundary >> simp[],
     drule_all pop_compile_tuple_store_all_boundary >> simp[],
     gvs[comp_return_def]]
QED

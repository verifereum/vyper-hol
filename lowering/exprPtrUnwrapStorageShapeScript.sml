(* Exceptional produced types are never returned at storage locations. *)
Theory exprPtrUnwrapStorageShape
Ancestors
  exprLowering compileEnv context abiBuiltinDispatchCorrect

Theorem compile_literal_located_memory[local]:
  compile_literal_vv ty lit sa = (LocatedValue t p,sb) ==> p.ptr_location = LocMemory
Proof
  Cases_on `lit` >> simp[compile_literal_vv_def, AllCaseEqs(),
    comp_return_def, comp_bind_def, base_ptr_def, mk_ptr_def] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `b` >> gvs[compile_literal_vv_def, comp_return_def])
  >- (pairarg_tac >> gvs[]) >>
  Cases_on `ty` >> gvs[comp_return_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> gvs[comp_return_def] >>
  rename1 `BytesT len` >> Cases_on `len` >>
  gvs[comp_return_def, comp_bind_def] >> pairarg_tac >> gvs[]
QED

Theorem compile_intcall_located_memory[local]:
  compile_call cfn cenv ret ty (IntCall fid) args default sa = (LocatedValue t p,sb) ==>
  p.ptr_location = LocMemory
Proof
  simp[compile_call_def] >> rpt (pairarg_tac >> gvs[]) >>
  simp[AllCaseEqs(), base_ptr_def, mk_ptr_def] >>
  rpt strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), base_ptr_def, mk_ptr_def]
QED

Theorem compile_abiencode_located_memory[local]:
  compile_type_builtin_dispatch_body cfn cenv vt ty (AbiEncode ensure method)
    ret args sa = (LocatedValue t p,sb) ==> p.ptr_location = LocMemory
Proof
  simp[compile_type_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[AllCaseEqs(), as_ptr_val_def, mk_ptr_def] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  drule as_ptr_val_result >> strip_tac >> gvs[mk_ptr_def]
QED

Theorem compile_storage_lowered_value_type:
  compile_expr cenv ty e sa = (LocatedValue t p,sm) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
  lowered_value_type cenv e = expr_type e
Proof
  Cases_on `e` >> simp[lowered_value_type_def]
  >- (simp[Once compile_expr_raw_def, compile_expr_body_def] >>
      rpt strip_tac >> drule compile_literal_located_memory >> simp[])
  >- (rename1 `TypeBuiltin ann tb ret args` >> Cases_on `tb` >>
      simp[lowered_value_type_def] >>
      simp[Once compile_expr_component_eq] >>
      simp[Once compile_expr_raw_def] >> rpt strip_tac >>
      drule compile_abiencode_located_memory >> simp[]) >>
  rename1 `Call ann target args default` >> Cases_on `target` >>
  simp[lowered_value_type_def] >>
  simp[Once compile_expr_component_eq] >> rpt strip_tac >>
  drule compile_intcall_located_memory >> simp[]
QED

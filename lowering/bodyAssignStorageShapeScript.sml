(* Temporary worker: storage-backed result constructor boundaries. *)
Theory bodyAssignStorageShape
Ancestors
  bodySim exprLowering context compileEnv exprSimHyps vyperInterpreter
  vyperState vyperValue vyperAST pair finite_map
  exprReasonOperand exprSimSubscriptArrayOrigin bodyMemSnapshotSourceLocation

Theorem body_assign_attribute_storage_origin:
  compile_attribute f cenv rt ty obj fld sa = (LocatedValue t p,sb) /\
  p.ptr_location <> LocMemory ==>
  t = rt /\
  vv_location (FST (f cenv ty obj sa)) = SOME p.ptr_location
Proof
  Cases_on `f cenv ty obj sa` >> Cases_on `vv_location q` >>
  simp[compile_attribute_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> simp[mk_ptr_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem body_assign_subscript_storage_origin:
  compile_subscript f cenv rt ty obj idx sa = (LocatedValue t p,sb) /\
  p.ptr_location <> LocMemory ==>
  t = rt /\ ~copies_subscript_base cenv obj idx /\
  vv_location (FST (f cenv ty obj sa)) = SOME p.ptr_location
Proof
  Cases_on `f cenv ty obj sa` >>
  simp[compile_subscript_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `copies_subscript_base cenv obj idx` >> gvs[comp_return_def]
  >- (`vv_with_type (vv_type q) q = q` by
        (Cases_on `q` >> simp[vv_with_type_def, vv_type_def]) >>
      qpat_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
      qpat_assum `vv_with_type _ _ = _`
        (fn th => once_rewrite_tac [GSYM th]) >>
      disch_then (mp_tac o MATCH_MP snapshot_saved_representation) >>
      strip_tac >> Cases_on `is_word_type (vv_type q)` >> gvs[] >>
      Cases_on `place_type cenv obj` >>
      rpt BasicProvers.TOP_CASE_TAC >>
      simp[comp_bind_def, comp_return_def, LET_THM] >>
      rpt (pairarg_tac >> gvs[]) >>
      gvs[mk_ptr_def, AllCaseEqs()] >>
      rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[mk_ptr_def]) >>
  rename1 `f cenv ty obj sa = (bv,bs)` >>
  Cases_on `vv_location bv` >> Cases_on `place_type cenv obj` >>
  rpt BasicProvers.TOP_CASE_TAC >>
  simp[comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[mk_ptr_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[mk_ptr_def]
QED

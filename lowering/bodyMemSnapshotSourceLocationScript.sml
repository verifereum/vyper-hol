(* Imported source-location facts for retagged snapshots. *)
Theory bodyMemSnapshotSourceLocation
Ancestors
  exprSimConcatResult exprLowering loweringPosts context compileEnv vyperAST

Theorem snapshot_saved_representation:
  compile_snapshot_vv ce T (vv_with_type ty vv) sa = (saved,sb) ==>
  vv_type saved = ty /\
  vv_location saved = (if is_word_type ty then NONE else SOME LocMemory) /\
  unwrap_value ce saved st = (vv_operand saved,st)
Proof
  Cases_on `vv` >>
  simp[vv_with_type_def, vv_type_def, compile_snapshot_vv_def] >>
  Cases_on `is_word_type ty` >>
  simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[vv_type_def, vv_location_def, vv_operand_def, unwrap_value_def, mk_ptr_def,
      comp_return_def]
QED

Theorem snapshot_literal_location[local]:
  !t l sc vv sa. compile_literal_vv t l sc = (vv,sa) ==>
  vv_location vv = NONE \/ vv_location vv = SOME LocMemory
Proof
  rpt gen_tac >> Cases_on `l`
  >- (Cases_on `b` >> simp[compile_literal_vv_def, comp_return_def] >>
      strip_tac >> gvs[vv_location_def])
  >- (Cases_on `t` >> simp[compile_literal_vv_def, comp_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      strip_tac >> gvs[base_ptr_def, vv_location_def])
  >- (Cases_on `t` >> simp[compile_literal_vv_def, comp_bind_def, comp_return_def] >>
      rpt strip_tac >> gvs[vv_location_def] >>
      Cases_on `b` >> gvs[compile_literal_vv_def, comp_return_def, vv_location_def] >>
      Cases_on `b'` >> gvs[compile_literal_vv_def, comp_bind_def, comp_return_def, vv_location_def] >>
      rpt (pairarg_tac >> gvs[]) >> gvs[base_ptr_def, vv_location_def])
  >> simp[compile_literal_vv_def, comp_return_def] >>
  strip_tac >> gvs[vv_location_def]
QED

Theorem snapshot_changed_type_location:
  compile_expr ce ty e sc = (vv,sa) /\
  lowered_value_type ce e <> post_value_type ce e ==>
  vv_location vv = NONE \/ vv_location vv = SOME LocMemory
Proof
  Cases_on `e` >>
  simp[lowered_value_type_def, post_value_type_def, expr_type_def] >>
  rpt strip_tac
  >- (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      simp[Once compile_expr_def, compile_expr_body_def, expr_type_def] >>
      metis_tac[snapshot_literal_location])
  >- suspend "builtin"
  >- suspend "typebuiltin"
  >- suspend "call"
QED

Resume snapshot_changed_type_location[builtin]:
  Cases_on `b` >> gvs[lowered_value_type_def, expr_type_def] >>
  drule concat_compile_shape >> strip_tac >>
  gvs[vv_location_def, base_ptr_def]
QED

Resume snapshot_changed_type_location[typebuiltin]:
  Cases_on `t0` >> gvs[lowered_value_type_def, expr_type_def] >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_raw_def, compile_expr_body_def, expr_type_def,
       expr_size_def] >>
  simp[Once (cj 3 compile_expr_raw_def), compile_type_builtin_dispatch_body_def] >>
  rpt IF_CASES_TAC >> rpt (pairarg_tac >> gvs[]) >>
  simp[as_ptr_val_def] >> rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> gvs[oneline as_ptr_val_def, AllCaseEqs(), vv_location_def, mk_ptr_def]
QED

Resume snapshot_changed_type_location[call]:
  Cases_on `c` >> gvs[lowered_value_type_def, post_value_type_def, expr_type_def] >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def, compile_expr_body_def, expr_type_def,
       compile_call_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt IF_CASES_TAC >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> gvs[vv_location_def, base_ptr_def, AllCaseEqs()]
QED

Finalise snapshot_changed_type_location

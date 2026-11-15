(* Location-only compiler selector interfaces. *)
Theory bodyIntCallPostProvenanceOriginLocation
Ancestors exprLowering compileEnv context

Theorem origin_compile_attribute_location:
  (!s v u. f ce ty obj s = (v,u) ==> vv_location v = SOME loc) /\
  compile_attribute f ce ann ty obj fld sa = (vv,sb) ==>
  vv_location vv = SOME loc
Proof
  simp[compile_attribute_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[vv_location_def, mk_ptr_def]
QED

Theorem origin_compile_subscript_location:
  (!s v u. f ce ty obj s = (v,u) ==> vv_location v = SOME loc) /\
  ~copies_subscript_base ce obj idx /\
  compile_subscript f ce ann ty obj idx sa = (vv,sb) ==>
  vv_location vv = SOME loc
Proof
  strip_tac >>
  qpat_x_assum `compile_subscript _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_subscript_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  Cases_on `place_type ce obj`
  >- (gvs[comp_bind_def, comp_return_def, LET_THM] >>
      rpt (pairarg_tac >> gvs[]) >> gvs[vv_location_def, mk_ptr_def]) >>
  rename1 `place_type ce obj = ValPT bt` >> Cases_on `bt` >>
  gvs[comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[vv_location_def, mk_ptr_def]
QED

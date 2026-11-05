(* Compiler/source origin boundaries for framed array selection. *)
Theory exprSimSubscriptArrayOrigin
Ancestors
  exprSimSubscriptArraySource exprLowering vyperState vyperInterpreter
  vyperAST vyperValue vyperMisc pair vyperTypeContract vyperTypeSystem
  compileEnv finite_map

Theorem extend_storage_place_not_memory:
  extend_storage_place cx tr slot tv sb s = (INL p,t) ==>
  !id path. p <> MemoryPlace id path
Proof
  Cases_on `tv` >> Cases_on `sb` >>
  simp[oneline extend_storage_place_def, bind_def, ignore_bind_def,
       raise_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[value_CASE_rator, AllCaseEqs(), raise_def, return_def,
      bind_def, ignore_bind_def, UNCURRY]
QED

Theorem extend_place_memory_origin:
  extend_place cx r sb s = (INL (PlaceR (MemoryPlace id path)),t) ==>
  ?path0. r = PlaceR (MemoryPlace id path0)
Proof
  Cases_on `r` >> simp[extend_place_def, raise_def]
  >- (Cases_on `p` >>
      simp[extend_place_def, extend_memory_place_def, bind_def,
           ignore_bind_def, return_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      drule extend_storage_place_not_memory >> simp[]) >>
  Cases_on `sb` >>
  simp[extend_place_def, bind_def, lift_option_type_def, return_def,
       raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[value_type_CASE_rator, return_def, raise_def, bind_def, AllCaseEqs()]
QED

Theorem select_result_memory_origin:
  select_result cx ty r sb s = (INL (PlaceR (MemoryPlace id path)),t) ==>
  ?path0. r = PlaceR (MemoryPlace id path0)
Proof
  Cases_on `r` >>
  simp[select_result_def, bind_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> drule extend_place_memory_origin >> simp[]
QED

Theorem lookup_global_not_memory:
  lookup_global cx src id s = (INL r,t) ==>
  !name path. r <> PlaceR (MemoryPlace name path)
Proof
  simp[lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[option_CASE_rator, prod_CASE_rator, var_decl_info_CASE_rator,
      bind_def, lift_option_type_def, return_def, raise_def, AllCaseEqs()]
QED

Theorem eval_base_place_memory_origin:
  !bt cx s id path t.
    eval_base_place cx bt s = (INL (PlaceR (MemoryPlace id path)),t) ==>
    ~toplevel_target bt
Proof
  completeInduct_on `base_assignment_target_size bt` >>
  Cases_on `bt` >> rpt strip_tac >>
  gvs[toplevel_target_def, Once evaluate_def, bind_def, AllCaseEqs()]
  >- (PairCases_on `p` >> gvs[Once evaluate_def] >>
      drule lookup_global_not_memory >> simp[]) >>
  drule extend_place_memory_origin >> strip_tac >> gvs[] >>
  first_x_assum (qspec_then `base_assignment_target_size b` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qspec_then `b` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem compile_code_target_toplevel:
  !bt env vt cfn cenv st.
    type_place_target env bt = SOME vt /\
    (!id ty. FLOOKUP env.var_types id = SOME ty ==>
       ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
    FST (SND (FST (compile_get_target_ptr cfn cenv bt st))) = SOME LocCode ==>
    toplevel_target bt
Proof
  completeInduct_on `base_assignment_target_size bt` >>
  Cases_on `bt` >> rpt strip_tac >>
  gvs[toplevel_target_def]
  >- (gvs[Once well_typed_expr_def, AllCaseEqs()] >>
      first_x_assum drule >> strip_tac >>
      gvs[compile_get_target_ptr_def, comp_return_def]) >>
  gvs[Once well_typed_expr_def, AllCaseEqs()] >>
  rename1 `type_place_target env b = SOME root_vt` >>
  Cases_on `SND (SND (FST (compile_get_target_ptr cfn cenv b st)))` >>
  Cases_on `THE (SND (SND (FST (compile_get_target_ptr cfn cenv b st))))` >>
  gvs[Once compile_get_target_ptr_def, comp_bind_def, comp_return_def,
      LET_THM, UNCURRY] >>
  first_x_assum (qspec_then `base_assignment_target_size b` mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (qspec_then `b` mp_tac) >>
  simp[] >> disch_then irule >> goal_assum (drule_at Any) >>
  qexistsl [`env`, `root_vt`] >> simp[]
QED

Theorem code_target_not_memory:
  type_place_target env bt = SOME vt /\
  (!id ty. FLOOKUP env.var_types id = SOME ty ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
  FST (SND (FST (compile_get_target_ptr cfn cenv bt st))) = SOME LocCode /\
  eval_target_place cx bt s = (INL p,t) ==>
  !id path. p <> MemoryPlace id path
Proof
  strip_tac >> drule_all compile_code_target_toplevel >> strip_tac >>
  gvs[Once evaluate_def, bind_def, get_place_def, return_def, raise_def,
      AllCaseEqs()] >> rpt strip_tac >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  drule eval_base_place_memory_origin >> simp[]
QED

(* Compiler/source origin boundaries for framed array selection. *)
Theory exprSimSubscriptArrayOrigin
Ancestors
  exprSimSubscriptArraySource exprLowering vyperState vyperInterpreter
  vyperAST vyperValue vyperMisc pair vyperTypeContract vyperTypeSystem
  compileEnv finite_map context exprSafeOperandBuiltins

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

Theorem type_place_expr_not_memory:
  !e env vt cx s r t.
    type_place_expr env e = SOME vt /\ eval_expr cx e s = (INL r,t) ==>
    !id path. r <> PlaceR (MemoryPlace id path)
Proof
  completeInduct_on `expr_size e` >> Cases_on `e` >> rpt strip_tac >>
  gvs[Once well_typed_expr_def, AllCaseEqs()]
  >- (PairCases_on `p` >> gvs[Once evaluate_def] >>
      drule lookup_global_not_memory >> simp[]) >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  drule select_result_memory_origin >> strip_tac >> gvs[] >>
  rename1 `type_place_expr env obj = SOME obj_vt` >>
  first_x_assum (qspec_then `expr_size obj` mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (qspec_then `obj` mp_tac) >>
  simp[] >> metis_tac[]
QED


Theorem compile_subscript_code_origin:
  vv_location (FST (compile_subscript f cenv rt ty obj idx sa)) = SOME LocCode ==>
  vv_location (FST (f cenv ty obj sa)) = SOME LocCode
Proof
  Cases_on `f cenv ty obj sa` >>
  Cases_on `vv_location q` >>
  Cases_on `place_type cenv obj` >>
  simp[compile_subscript_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[vv_location_def, mk_ptr_def] >>
  Cases_on `t` >> simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[vv_location_def, mk_ptr_def]
QED

Theorem compile_attribute_code_origin:
  vv_location (FST (compile_attribute f cenv rt ty obj fld sa)) = SOME LocCode ==>
  vv_location (FST (f cenv ty obj sa)) = SOME LocCode
Proof
  Cases_on `f cenv ty obj sa` >> Cases_on `vv_location q` >>
  simp[compile_attribute_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> simp[vv_location_def, mk_ptr_def]
QED

Theorem compile_ifexp_not_code:
  vv_location (FST (compile_expr_body f g h cenv ty
    (IfExp ann cond th el) sa)) <> SOME LocCode
Proof
  simp[compile_expr_body_def, expr_type_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[AllCaseEqs(), vv_location_def, mk_ptr_def] >>
  Cases_on `is_word_type ann` >> simp[vv_location_def, mk_ptr_def]
QED


Theorem compile_call_not_code:
  vv_location (FST (compile_call f cenv rt ty target args dflt sa)) <> SOME LocCode
Proof
  Cases_on `target`
  >~ [`RawCallTarget rcf`] >-
    (namedCases_on `args` ["", "addr tail"] >> simp[compile_call_def, LET_THM] >>
     rpt (pairarg_tac >> gvs[]) >> simp[vv_location_def] >>
     Cases_on `tail` >>
     simp[compile_call_def, LET_THM] >> rpt (pairarg_tac >> gvs[]) >>
     simp[vv_location_def] >>
     IF_CASES_TAC >> simp[vv_location_def, mk_ptr_def])
  >~ [`RawCallCalldataTarget rcf`] >-
    (Cases_on `args` >> simp[compile_call_def, LET_THM] >>
     rpt (pairarg_tac >> gvs[]) >> simp[vv_location_def] >>
     IF_CASES_TAC >> simp[vv_location_def, mk_ptr_def])
  >~ [`CreateTarget ck salted rof code`] >-
    (Cases_on `compile_create_call f cenv ck salted rof args sa` >>
     simp[compile_call_def, as_stack_val_def, vv_location_def]) >>
  simp[compile_call_def, LET_THM] >> rpt (pairarg_tac >> gvs[]) >>
  simp[vv_location_def, mk_ptr_def, base_ptr_def]
  >~ [`cenv.ce_func_info nm = _`] >-
    (Cases_on `returns_count > 0` >> Cases_on `return_buf` >>
     gvs[] >> rpt (pairarg_tac >> gvs[]) >> simp[vv_location_def])
  >~ [`ExtCall b b0 sig opts`] >-
    (PairCases_on `sig` >> Cases_on `args` >>
     simp[compile_call_def, LET_THM] >> rpt (pairarg_tac >> gvs[]) >>
     gvs[AllCaseEqs(), vv_location_def, mk_ptr_def] >>
     IF_CASES_TAC >> simp[vv_location_def]) >>
  namedCases_on `args` ["", "addr tail"] >> simp[vv_location_def] >>
  Cases_on `tail` >> simp[vv_location_def] >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >> simp[vv_location_def] >>
  IF_CASES_TAC >> simp[vv_location_def]
QED

Theorem code_expr_not_memory:
  !e env cenv ty sa cx s r t.
    well_typed_expr env e /\
    (!id vt. FLOOKUP env.var_types id = SOME vt ==>
       ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
    vv_location (FST (compile_expr cenv ty e sa)) = SOME LocCode /\
    eval_expr cx e s = (INL r,t) ==>
    !id path. r <> PlaceR (MemoryPlace id path)
Proof
  completeInduct_on `expr_size e` >> Cases_on `e` >> rpt strip_tac
  >~ [`well_typed_expr env (Name ann nm)`] >-
    (qpat_x_assum `!m. m < _ ==> _` kall_tac >>
     gvs[Once well_typed_expr_def] >>
     qpat_x_assum `!id vt. _` drule >> strip_tac >>
     gvs[Once compile_expr_def, compile_expr_body_def, compile_name_vv_def,
         comp_return_def, vv_location_def, mk_ptr_def, expr_type_def])
  >~ [`eval_expr cx (TopLevelName ann nsid) _ = _`] >-
    (PairCases_on `nsid` >> gvs[Once evaluate_def] >>
     drule lookup_global_not_memory >> simp[])
  >~ [`eval_expr cx (Literal ann lit) _ = _`] >-
    gvs[Once evaluate_def, return_def]
  >~ [`eval_expr cx (Subscript ann obj idx) _ = _`] >- suspend "subscript"
  >~ [`eval_expr cx (Attribute ann obj fld) _ = _`] >- suspend "attribute"
  >~ [`eval_expr cx (Pop ann bt) _ = _`] >- suspend "pop" >>
  qpat_x_assum `!m. m < _ ==> _` kall_tac
  >~ [`eval_expr cx (FlagMember ann nsid fld) _ = _`] >-
    gvs[Once compile_expr_def, compile_expr_body_def, expr_type_def,
        comp_return_def, vv_location_def]
  >~ [`eval_expr cx (IfExp ann cond th el) _ = _`] >-
    (qpat_x_assum `vv_location _ = _` mp_tac >>
     simp[Once (CONJUNCT1 compile_expr_raw_def), compile_ifexp_not_code])
  >~ [`eval_expr cx (Call ann dest args dflt) _ = _`] >-
    (qpat_x_assum `vv_location _ = _` mp_tac >>
     simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
          compile_call_not_code]) >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, return_def,
      raise_def, AllCaseEqs()] >>
  rename1 `StructLit ann nsid fields` >> PairCases_on `nsid` >>
  gvs[Once evaluate_def, bind_def, return_def, AllCaseEqs()]
QED

Resume code_expr_not_memory[subscript]:
  qpat_x_assum `vv_location _ = _` mp_tac >>
  pure_once_rewrite_tac [CONJUNCT1 compile_expr_raw_def] >>
  simp[compile_expr_body_def, expr_type_def] >>
  disch_then (mp_tac o MATCH_MP compile_subscript_code_origin) >>
  simp[exprCallBoundsTheory.expr_child_callback_def, expr_size_def] >>
  strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  drule select_result_memory_origin >> strip_tac >> gvs[] >>
  fs[Once well_typed_expr_def]
  >~ [`type_place_expr env obj = SOME vt`] >-
    (drule_all type_place_expr_not_memory >> simp[]) >>
  first_x_assum (qspec_then `expr_size obj` mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (qspec_then `obj` mp_tac) >>
  disch_then (drule_all o SRULE []) >> simp[]
QED
Resume code_expr_not_memory[attribute]:
  qpat_x_assum `vv_location _ = _` mp_tac >>
  pure_once_rewrite_tac [CONJUNCT1 compile_expr_raw_def] >>
  simp[compile_expr_body_def, expr_type_def] >>
  disch_then (mp_tac o MATCH_MP compile_attribute_code_origin) >>
  simp[exprCallBoundsTheory.expr_child_callback_def, expr_size_def] >>
  strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  drule select_result_memory_origin >> strip_tac >> gvs[] >>
  fs[Once well_typed_expr_def] >>
  first_x_assum (qspec_then `expr_size obj` mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (qspec_then `obj` mp_tac) >>
  disch_then (drule_all o SRULE []) >> simp[]
QED
Resume code_expr_not_memory[pop]:
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  qpat_x_assum `vv_location _ = _` mp_tac >>
  pure_once_rewrite_tac [CONJUNCT1 compile_expr_raw_def] >>
  simp[compile_expr_body_def, expr_type_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[vv_location_def, mk_ptr_def, AllCaseEqs()] >> strip_tac >>
  gvs[Once well_typed_expr_def, Once evaluate_def, bind_def, AllCaseEqs()] >>
  qmatch_asmsub_abbrev_tac `compile_get_target_ptr cb cenv bt sa` >>
  `FST (SND (FST (compile_get_target_ptr cb cenv bt sa))) = SOME LocCode`
    by simp[] >>
  drule_all code_target_not_memory >> strip_tac >>
  Cases_on `p` >> gvs[oneline pop_place_def, bind_def, ignore_bind_def,
    return_def, raise_def, AllCaseEqs()] >>
  rename1 `StoragePlace tr slot tv` >> Cases_on `tv` >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  rename1 `ArrayTV et bd` >> Cases_on `bd` >> gvs[bind_def, ignore_bind_def, return_def, raise_def,
    AllCaseEqs()]
QED
Finalise code_expr_not_memory

Theorem expr_body_pre_code_not_memory:
  expr_body_pre cenv cx env e es /\
  vv_location (FST (compile_expr cenv ty e sa)) = SOME LocCode /\
  eval_expr cx e s = (INL r,t) ==>
  !id path. r <> PlaceR (MemoryPlace id path)
Proof
  strip_tac >>
  irule code_expr_not_memory >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  qexists_tac `env` >>
  gvs[exprSimHypsDefsTheory.expr_body_pre_def,
      exprSimHypsDefsTheory.expr_sim_inv_def]
QED


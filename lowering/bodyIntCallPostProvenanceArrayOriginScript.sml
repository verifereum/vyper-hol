(* Source-origin probes: conditionals materialize storage values rather than
   returning their places. These facts do not infer source origin from bytes. *)
Theory bodyIntCallPostProvenanceArrayOrigin
Ancestors vyperInterpreter vyperState pair exprSimSubscriptMap
  compileEnv context vyperMisc supportedExprTraverse bodyIntCallPostProvenanceCapture
  exprLowering loweringStateRelDefs bodyIntCallPostProvenanceCaptureAlignment
  bodyIntCallPostProvenanceOriginLocation

Theorem conditional_result_nonstorage:
  conditional_result cx raw es = (INL tv,ee) ==>
  !tr slot vt. tv <> PlaceR (StoragePlace tr slot vt)
Proof
  Cases_on `raw`
  >~ [`Value v`] >- (simp[conditional_result_def, return_def] >> rpt strip_tac >> gvs[])
  >~ [`HashMapRef tr slot kt vt`] >- simp[conditional_result_def, raise_def] >>
  rename1 `PlaceR p` >> Cases_on `p` >>
  simp[conditional_result_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  IF_CASES_TAC >> simp[bind_def, return_def, AllCaseEqs()]
QED

Theorem select_result_nonstorage_origin:
  select_result cx ty raw sb es = (INL out,ee) /\
  (!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)) /\
  (!tr slot kt vt. raw <> HashMapRef tr slot kt vt) ==>
  (!tr slot vt. out <> PlaceR (StoragePlace tr slot vt)) /\
  (!tr slot kt vt. out <> HashMapRef tr slot kt vt)
Proof
  Cases_on `raw`
  >~ [`HashMapRef tr slot kt vt`] >- metis_tac[]
  >~ [`Value v`] >-
    (simp[select_result_def, bind_def, return_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[]) >>
  rename1 `PlaceR p` >> Cases_on `p`
  >~ [`StoragePlace tr slot vt`] >- metis_tac[] >>
  simp[select_result_def, extend_place_def, extend_memory_place_def,
       bind_def, ignore_bind_def, return_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem conditional_result_nonmapping:
  conditional_result cx raw es = (INL tv,ee) ==>
  !tr slot kt vt. tv <> HashMapRef tr slot kt vt
Proof
  Cases_on `raw`
  >~ [`Value v`] >- (simp[conditional_result_def, return_def] >> rpt strip_tac >> gvs[])
  >~ [`HashMapRef tr slot kt vt`] >- simp[conditional_result_def, raise_def] >>
  rename1 `PlaceR p` >> Cases_on `p` >>
  simp[conditional_result_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  IF_CASES_TAC >> simp[bind_def, return_def, AllCaseEqs()]
QED

Theorem origin_toplevel_storage_location:
  storage_vars_rel ce cx /\ transient_vars_rel ce cx /\
  lookup_global cx src id es = (INL raw,ee) /\
  compile_expr ce ty (TopLevelName ann (src,id)) sa = (vv,sb) /\
  ((?tr slot vt. raw = PlaceR (StoragePlace tr slot vt)) \/
   (?tr slot kt vt. raw = HashMapRef tr slot kt vt)) ==>
  ?loc. (loc = LocStorage \/ loc = LocTransient) /\ vv_location vv = SOME loc
Proof
  simp[lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[option_CASE_rator, prod_CASE_rator, var_decl_info_CASE_rator,
      bind_def, lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
  drule_at (Pat `find_var_decl_by_name _ _ = _`) toplevel_storage_ce_vars_decl >>
  simp[var_decl_transient_def] >> disch_then drule_all >> strip_tac >>
  gvs[compile_expr_def, vyperASTTheory.expr_type_def] >>
  Cases_on `tr` >> gvs[vv_location_def, mk_ptr_def]
QED

Theorem origin_compile_attribute_location_at:
  f ce ty obj sa = (bvv,sm) /\ vv_location bvv = SOME loc /\
  compile_attribute f ce ann ty obj fld sa = (vv,sb) ==>
  vv_location vv = SOME loc
Proof
  strip_tac >>
  qpat_x_assum `compile_attribute _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_attribute_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[vv_location_def, mk_ptr_def]
QED

Theorem origin_compile_subscript_location_at:
  f ce ty obj sa = (bvv,sm) /\ vv_location bvv = SOME loc /\
  ~copies_subscript_base ce obj idx /\
  compile_subscript f ce ann ty obj idx sa = (vv,sb) ==>
  vv_location vv = SOME loc
Proof
  strip_tac >>
  qpat_x_assum `compile_subscript _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_subscript_def, comp_bind_def, comp_return_def, LET_THM] >>
  Cases_on `place_type ce obj`
  >- (simp[comp_bind_def, comp_return_def, LET_THM] >>
      rpt (pairarg_tac >> gvs[]) >> strip_tac >>
      gvs[vv_location_def, mk_ptr_def]) >>
  rename1 `place_type ce obj = ValPT bt` >> Cases_on `bt` >>
  simp[comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[vv_location_def, mk_ptr_def]
QED

Theorem intcall_source_storage_location:
  !e ty sa sb vv es ee raw.
  storage_vars_rel ce cx /\ transient_vars_rel ce cx /\
  ce.ce_modules = (case ALOOKUP cx.sources cx.txn.target of NONE => [] | SOME mods => mods) /\
  ~expr_has_effect e /\ eval_expr cx e es = (INL raw,ee) /\
  compile_expr ce ty e sa = (vv,sb) /\
  ((?tr slot vt. raw = PlaceR (StoragePlace tr slot vt)) \/
   (?tr slot kt vt. raw = HashMapRef tr slot kt vt)) ==>
  ?loc. (loc = LocStorage \/ loc = LocTransient) /\ vv_location vv = SOME loc
Proof
  completeInduct_on `expr_size e` >> Cases_on `e` >> rpt strip_tac
  >>~- ([`eval_expr cx (TopLevelName ann nsid) _ = _`],
    PairCases_on `nsid` >>
    qpat_x_assum `eval_expr cx (TopLevelName _ _) _ = _` mp_tac >>
    simp[Once evaluate_def] >> strip_tac >>
    metis_tac[origin_toplevel_storage_location])
  >>~- ([`eval_expr cx (Subscript ann obj idx) _ = _`], suspend "subscript")
  >>~- ([`eval_expr cx (Attribute ann obj fld) _ = _`], suspend "attribute")
  >>~- ([`eval_expr cx (IfExp ann cond th el) _ = _`],
    qpat_x_assum `!m. m < _ ==> _` kall_tac >>
    qpat_x_assum `eval_expr cx (IfExp _ _ _ _) _ = _` mp_tac >>
    simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
    metis_tac[conditional_result_nonstorage, conditional_result_nonmapping])
  >>~- ([`eval_expr cx (Call ann dest args dflt) _ = _`],
    gvs[expr_has_effect_def, supported_expr_exists_def, expr_effect_root_def])
  >>~- ([`eval_expr cx (FlagMember ann nsid fld) _ = _`],
    PairCases_on `nsid` >>
    qpat_x_assum `eval_expr cx _ _ = _` mp_tac >>
    simp[Once evaluate_def, lookup_flag_mem_def, bind_def, return_def,
         raise_def, lift_option_type_def, option_CASE_rator, AllCaseEqs()])
  >>~- ([`eval_expr cx (StructLit ann nsid fields) _ = _`],
    PairCases_on `nsid` >>
    qpat_x_assum `eval_expr cx _ _ = _` mp_tac >>
    simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()])
  >>~- ([`eval_expr cx (Pop ann bt) _ = _`],
    gvs[expr_has_effect_def, supported_expr_exists_def, expr_effect_root_def]) >>
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  qpat_x_assum `eval_expr cx _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def,
       raise_def, lookup_flag_mem_def, lift_option_type_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[lookup_flag_mem_def, bind_def, return_def,
                         raise_def, lift_option_type_def, AllCaseEqs()]
QED

Resume intcall_source_storage_location[attribute]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  qpat_x_assum `eval_expr cx (Attribute _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  `(?tr sl vt. res = PlaceR (StoragePlace tr sl vt)) \/
   (?tr sl kt vt. res = HashMapRef tr sl kt vt)` by
    metis_tac[select_result_nonstorage_origin] >>
  Cases_on `compile_expr ce ty obj sa` >>
  first_x_assum (qspec_then `expr_size obj` mp_tac) >>
  simp[vyperASTTheory.expr_size_def] >>
  disch_then (qspec_then `obj` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`ty`,`sa`,`r`,`q`,`es`,`s''`,`res`] mp_tac) >>
  simp[expr_has_effect_def, supported_expr_exists_def, expr_effect_root_def] >>
  gvs[expr_has_effect_def, supported_expr_exists_def, expr_effect_root_def] >>
  strip_tac >> qexists_tac `loc` >> simp[] >>
  qpat_x_assum `compile_expr ce ty (Attribute _ _ _) _ = _` mp_tac >>
  simp[Once compile_expr_def] >> strip_tac >>
  drule_at (Pat `compile_attribute _ _ _ _ _ _ _ = _`)
    origin_compile_attribute_location_at >>
  simp[exprCallBoundsTheory.expr_child_callback_def] >>
  disch_then drule_all >> simp[]
QED

Resume intcall_source_storage_location[subscript]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  `(?tr sl vt. res' = PlaceR (StoragePlace tr sl vt)) \/
   (?tr sl kt vt. res' = HashMapRef tr sl kt vt)` by
    metis_tac[select_result_nonstorage_origin] >>
  Cases_on `subscript_reads_base cx obj idx` >>
  gvs[bind_def, return_def, AllCaseEqs()] >>
  rename1 `eval_expr cx obj es = (INL braw,be)` >>
  `(?tr sl vt. braw = PlaceR (StoragePlace tr sl vt)) \/
   (?tr sl kt vt. braw = HashMapRef tr sl kt vt)` by
    metis_tac[select_result_nonstorage_origin] >>
  Cases_on `compile_expr ce ty obj sa` >>
  first_x_assum (qspec_then `expr_size obj` mp_tac) >>
  simp[] >> disch_then (qspec_then `obj` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`ty`,`sa`,`r`,`q`,`es`,`be`,`braw`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `loc` >> simp[] >>
  qpat_x_assum `compile_expr ce ty (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once compile_expr_def] >> strip_tac >>
  drule_at (Pat `compile_subscript _ _ _ _ _ _ _ = _`)
    origin_compile_subscript_location_at >>
  simp[exprCallBoundsTheory.expr_child_callback_def] >>
  `~copies_subscript_base ce obj idx` by
    (gvs[copies_subscript_base_def, subscript_reads_base_def]) >>
  disch_then drule_all >> simp[]
QED

Finalise intcall_source_storage_location

Theorem intcall_array_base_nonstorage:
  storage_vars_rel ce cx /\ transient_vars_rel ce cx /\
  ce.ce_modules = (case ALOOKUP cx.sources cx.txn.target of NONE => [] | SOME mods => mods) /\
  ~expr_has_effect e /\ eval_expr cx e es = (INL raw,ee) /\
  compile_expr ce ty e sa = (vv,sb) /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/
   vv_location vv = SOME LocCode) ==>
  !tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)
Proof
  rpt strip_tac >>
  drule_at (Pat `compile_expr _ _ _ _ = _`) intcall_source_storage_location >>
  disch_then (qspecl_then [`cx`,`es`,`ee`,`raw`] mp_tac) >> simp[]
QED

Theorem origin_capture_lookup[local]:
  (!src. ALOOKUP ce.ce_modules src = get_module_code cx src) /\
  ~expr_has_effect obj /\ ~expr_has_effect idx ==>
  (copies_subscript_base ce obj idx <=> subscript_reads_base cx obj idx)
Proof
  strip_tac >> simp[copies_subscript_base_def, subscript_reads_base_def] >>
  irule effect_free_subscript_overlap_lookup_cong >> simp[] >>
  gen_tac >> simp[vyperContextTheory.get_module_code_def] >>
  Cases_on `ALOOKUP cx.sources cx.txn.target` >>
  gvs[vyperContextTheory.get_module_code_def]
QED

Theorem intcall_source_storage_location_lookup:
  !e ty sa sb vv es ee raw.
  storage_vars_rel ce cx /\ transient_vars_rel ce cx /\
  (!src. ALOOKUP ce.ce_modules src = get_module_code cx src) /\
  ~expr_has_effect e /\ eval_expr cx e es = (INL raw,ee) /\
  compile_expr ce ty e sa = (vv,sb) /\
  ((?tr slot vt. raw = PlaceR (StoragePlace tr slot vt)) \/
   (?tr slot kt vt. raw = HashMapRef tr slot kt vt)) ==>
  ?loc. (loc = LocStorage \/ loc = LocTransient) /\ vv_location vv = SOME loc
Proof
  completeInduct_on `expr_size e` >> Cases_on `e` >> rpt strip_tac
  >>~- ([`eval_expr cx (TopLevelName ann nsid) _ = _`],
    PairCases_on `nsid` >>
    qpat_x_assum `eval_expr cx (TopLevelName _ _) _ = _` mp_tac >>
    simp[Once evaluate_def] >> strip_tac >>
    metis_tac[origin_toplevel_storage_location])
  >>~- ([`eval_expr cx (Subscript ann obj idx) _ = _`], suspend "subscript")
  >>~- ([`eval_expr cx (Attribute ann obj fld) _ = _`], suspend "attribute")
  >>~- ([`eval_expr cx (IfExp ann cond th el) _ = _`],
    qpat_x_assum `!m. m < _ ==> _` kall_tac >>
    qpat_x_assum `eval_expr cx (IfExp _ _ _ _) _ = _` mp_tac >>
    simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
    metis_tac[conditional_result_nonstorage, conditional_result_nonmapping])
  >>~- ([`eval_expr cx (Call ann dest args dflt) _ = _`],
    gvs[expr_has_effect_def, supported_expr_exists_def, expr_effect_root_def])
  >>~- ([`eval_expr cx (FlagMember ann nsid fld) _ = _`],
    PairCases_on `nsid` >> qpat_x_assum `eval_expr cx _ _ = _` mp_tac >>
    simp[Once evaluate_def, lookup_flag_mem_def, bind_def, return_def,
         raise_def, lift_option_type_def, option_CASE_rator, AllCaseEqs()])
  >>~- ([`eval_expr cx (StructLit ann nsid fields) _ = _`],
    PairCases_on `nsid` >> qpat_x_assum `eval_expr cx _ _ = _` mp_tac >>
    simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()])
  >>~- ([`eval_expr cx (Pop ann bt) _ = _`],
    gvs[expr_has_effect_def, supported_expr_exists_def, expr_effect_root_def]) >>
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  qpat_x_assum `eval_expr cx _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def,
       raise_def, lookup_flag_mem_def, lift_option_type_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[lookup_flag_mem_def, bind_def, return_def,
                         raise_def, lift_option_type_def, AllCaseEqs()]
QED

Resume intcall_source_storage_location_lookup[attribute]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  qpat_x_assum `eval_expr cx (Attribute _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  `(?tr sl vt. res = PlaceR (StoragePlace tr sl vt)) \/
   (?tr sl kt vt. res = HashMapRef tr sl kt vt)` by
    metis_tac[select_result_nonstorage_origin] >>
  Cases_on `compile_expr ce ty obj sa` >>
  first_x_assum (qspec_then `expr_size obj` mp_tac) >>
  simp[vyperASTTheory.expr_size_def] >>
  disch_then (qspec_then `obj` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`ty`,`sa`,`r`,`q`,`es`,`s''`,`res`] mp_tac) >>
  simp[expr_has_effect_def, supported_expr_exists_def, expr_effect_root_def] >>
  gvs[expr_has_effect_def, supported_expr_exists_def, expr_effect_root_def] >>
  strip_tac >> qexists_tac `loc` >> simp[] >>
  qpat_x_assum `compile_expr ce ty (Attribute _ _ _) _ = _` mp_tac >>
  simp[Once compile_expr_def] >> strip_tac >>
  drule_at (Pat `compile_attribute _ _ _ _ _ _ _ = _`)
    origin_compile_attribute_location_at >>
  simp[exprCallBoundsTheory.expr_child_callback_def] >>
  disch_then drule_all >> simp[]
QED

Resume intcall_source_storage_location_lookup[subscript]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  `(?tr sl vt. res' = PlaceR (StoragePlace tr sl vt)) \/
   (?tr sl kt vt. res' = HashMapRef tr sl kt vt)` by
    metis_tac[select_result_nonstorage_origin] >>
  Cases_on `subscript_reads_base cx obj idx` >>
  gvs[bind_def, return_def, AllCaseEqs()] >>
  rename1 `eval_expr cx obj es = (INL braw,be)` >>
  `(?tr sl vt. braw = PlaceR (StoragePlace tr sl vt)) \/
   (?tr sl kt vt. braw = HashMapRef tr sl kt vt)` by
    metis_tac[select_result_nonstorage_origin] >>
  Cases_on `compile_expr ce ty obj sa` >>
  first_x_assum (qspec_then `expr_size obj` mp_tac) >>
  simp[] >> disch_then (qspec_then `obj` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`ty`,`sa`,`r`,`q`,`es`,`be`,`braw`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `loc` >> simp[] >>
  qpat_x_assum `compile_expr ce ty (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once compile_expr_def] >> strip_tac >>
  drule_at (Pat `compile_subscript _ _ _ _ _ _ _ = _`)
    origin_compile_subscript_location_at >>
  simp[exprCallBoundsTheory.expr_child_callback_def] >>
  `~expr_has_effect obj /\ ~expr_has_effect idx` by
    gvs[expr_has_effect_def, supported_expr_exists_def, expr_effect_root_def] >>
  `~copies_subscript_base ce obj idx` by metis_tac[origin_capture_lookup] >>
  disch_then drule_all >> simp[]
QED

Finalise intcall_source_storage_location_lookup

Theorem intcall_array_base_nonstorage_lookup:
  storage_vars_rel ce cx /\ transient_vars_rel ce cx /\
  (!src. ALOOKUP ce.ce_modules src = get_module_code cx src) /\
  ~expr_has_effect e /\ eval_expr cx e es = (INL raw,ee) /\
  compile_expr ce ty e sa = (vv,sb) /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/
   vv_location vv = SOME LocCode) ==>
  !tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)
Proof
  rpt strip_tac >>
  drule_at (Pat `compile_expr _ _ _ _ = _`) intcall_source_storage_location_lookup >>
  disch_then (qspecl_then [`cx`,`es`,`ee`,`raw`] mp_tac) >> simp[]
QED

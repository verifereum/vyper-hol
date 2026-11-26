(* Direct source selection at the endpoint of an array iterator expression.
   Unlike a successful read, this does not use popped memory history. *)
Theory bodyForArrayHeldDirectSelectionMods
Ancestors
  bodyFullForArray vyperAST vyperInterpreter vyperState vyperTypeSystem
  stmtSimForArrayFrame exprSimSubscriptArrayOrigin targetSubscriptMemory
  vyperLocalAccessFrame vyperStatePreservation exprSimIfExp[qualified,ignore_grammar]

Theorem held_eval_direct_selection_mods:
  !a ctx0 en zs name path ze.
    well_typed_expr en a /\ expr_writes_ok (\_. F) a /\
    eval_expr ctx0 a zs = (INL (PlaceR (MemoryPlace name path)),ze) ==>
    ?entry v. lookup_scopes name ze.scopes = SOME entry /\
              evaluate_subscripts entry.type entry.value path = INL v
Proof
  completeInduct_on `expr_size a` >>
  Cases_on `a` >> simp[] >> rpt strip_tac
  >~ [`eval_expr _ (Name _ _) _ = _`]
  >- (qpat_x_assum `eval_expr _ (Name _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, get_scopes_def, type_check_def, assert_def,
           bind_def, ignore_bind_def, return_def, raise_def, AllCaseEqs(),
           optionTheory.IS_SOME_EXISTS, evaluate_subscripts_def] >>
      strip_tac >> gvs[] >> metis_tac[])
  >~ [`eval_expr _ (TopLevelName _ _) _ = _`]
  >- (rename1 `eval_expr _ (TopLevelName _ nid) _ = _` >>
      PairCases_on `nid` >>
      qpat_x_assum `eval_expr _ (TopLevelName _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, lookup_global_not_memory])
  >~ [`eval_expr _ (Subscript _ _ _) _ = _`]
  >- suspend "subscript"
  >~ [`eval_expr _ (Attribute _ _ _) _ = _`]
  >- suspend "attribute"
  >~ [`eval_expr _ (IfExp _ _ _ _) _ = _`]
  >- suspend "conditional" >>
  drule_at (Pat `eval_expr _ _ _ = _`)
    bodyFullForArrayTheory.eval_iterator_memory_place_access >>
  simp[vyperTypeSystemTheory.expr_places_def]
QED

Resume held_eval_direct_selection_mods[subscript]:
  rename1 `eval_expr ctx0 (Subscript ann obj key) zs = _` >>
  Cases_on `subscript_reads_base ctx0 obj key` >>
  qpat_x_assum `eval_expr ctx0 (Subscript ann obj key) zs = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >>
  drule exprSimSubscriptArrayOriginTheory.select_result_memory_origin >>
  strip_tac >> gvs[] >>
  suspend "subscript_frame"
QED

Resume held_eval_direct_selection_mods[subscript_frame]:
  rename1 `eval_expr ctx0 obj zs = (INL (PlaceR (MemoryPlace name path0)),zm)` >>
  rename1 `eval_expr ctx0 key zm = (INL idx,zk)` >>
  rename1 `read_result ctx0 idx zk = (INL kv,zr)` >>
  `zr = zk` by (drule read_result_state >> simp[]) >>
  qpat_x_assum `zr = zk` SUBST_ALL_TAC >>
  `well_typed_expr en obj /\ well_typed_expr en key` by
    (qpat_assum `well_typed_expr en (Subscript ann obj key)` mp_tac >>
     simp[Once well_typed_expr_def, NoAsms] >> rpt strip_tac >>
     drule_all exprSimSubscriptArrayOriginTheory.type_place_expr_not_memory >>
     simp[]) >>
  `expr_writes_ok (\_. F) obj /\ expr_writes_ok (\_. F) key` by
    (qpat_assum `expr_writes_ok _ (Subscript ann obj key)` mp_tac >>
     simp[expr_writes_ok_def, NoAsms]) >>
  `expr_writes_ok (\w. FST (place_access w []) <> NameTarget name) key` by
    (drule_at (Pat `well_typed_expr _ _`)
       (Q.SPECL [`en`,`key`] (cj 1 stmtSimForArrayFrameTheory.writes_ok_typed_mono)) >>
     disch_then (qspecl_then
       [`\_. F`,`\w. FST (place_access w []) <> NameTarget name`] mp_tac) >>
     simp[]) >>
  `lookup_scopes name zk.scopes = lookup_scopes name zm.scopes` by
    (irule stmtSimForArrayFrameTheory.scope_projection_lookup >>
     qspecl_then [`ctx0`,`key`] mp_tac
       (cj 5 (Q.SPEC `name` stmtSimForArrayFrameTheory.eval_name_projection_mutual)) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (qspecl_then [`zm`,`INL idx`,`zk`] mp_tac) >> simp[]) >>
  qpat_assum `!m. m < _ ==> _` (qspec_then `expr_size obj` mp_tac) >>
  impl_tac >- decide_tac >>
  disch_then (qspec_then `obj` mp_tac) >> simp[NoAsms] >>
  disch_then drule_all >>
  disch_then (qx_choosel_then [`en0`,`v0`] (map_every assume_tac o CONJUNCTS)) >>
  `lookup_scopes name zk.scopes = SOME en0` by
    (qpat_assum `lookup_scopes name zk.scopes = lookup_scopes name zm.scopes`
       SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qpat_assum `select_result _ _ _ _ _ = _`
    (assume_tac o REWRITE_RULE [select_result_def]) >>
  drule_all targetSubscriptMemoryTheory.extend_place_memory_live >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Resume held_eval_direct_selection_mods[attribute]:
  rename1 `eval_expr ctx0 (Attribute ann obj attrId) zs = _` >>
  qpat_x_assum `eval_expr ctx0 (Attribute ann obj attrId) zs = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >>
  drule exprSimSubscriptArrayOriginTheory.select_result_memory_origin >>
  strip_tac >> gvs[] >>
  suspend "attribute_base"
QED

Resume held_eval_direct_selection_mods[attribute_base]:
  rename1 `eval_expr ctx0 obj zs = (INL (PlaceR (MemoryPlace name path0)),zm)` >>
  `well_typed_expr en obj` by
    (qpat_assum `well_typed_expr en (Attribute ann obj attrId)` mp_tac >>
     simp[Once well_typed_expr_def,NoAsms]) >>
  `expr_writes_ok (\_. F) obj` by
    (qpat_assum `expr_writes_ok _ (Attribute ann obj attrId)` mp_tac >>
     simp[expr_writes_ok_def,NoAsms]) >>
  qpat_assum `!m. m < _ ==> _` (qspec_then `expr_size obj` mp_tac) >>
  impl_tac >- decide_tac >>
  disch_then (qspec_then `obj` mp_tac) >> simp[NoAsms] >>
  disch_then drule_all >>
  disch_then (qx_choosel_then [`en0`,`v0`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `select_result _ _ _ _ _ = _`
    (assume_tac o REWRITE_RULE [select_result_def]) >>
  drule_all targetSubscriptMemoryTheory.extend_place_memory_live >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Resume held_eval_direct_selection_mods[conditional]:
  rename1 `eval_expr ctx0 (IfExp ann cond yes no) zs = _` >>
  `well_typed_expr en yes /\ well_typed_expr en no` by
    (qpat_assum `well_typed_expr en (IfExp ann cond yes no)` mp_tac >>
     simp[Once well_typed_expr_def, NoAsms]) >>
  qpat_x_assum `expr_writes_ok _ (IfExp ann cond yes no)`
    (strip_assume_tac o REWRITE_RULE [expr_writes_ok_def]) >>
  qpat_x_assum `eval_expr ctx0 (IfExp ann cond yes no) zs = _` mp_tac >>
  simp[Once evaluate_def, switch_BoolV_def, bind_def, return_def,
       raise_def, COND_RATOR, AllCaseEqs()] >> strip_tac >> gvs[] >>
  imp_res_tac vyperStatePreservationTheory.conditional_result_state >> gvs[] >>
  drule exprSimIfExpTheory.ifexp_conditional_result_shape >> simp[] >> strip_tac >> gvs[] >>
  rename1 `eval_expr ctx0 arm ms = (INL (PlaceR (MemoryPlace name path)),ze)` >>
  qpat_assum `!m. m < _ ==> _` (qspec_then `expr_size arm` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspec_then `arm` mp_tac) >> simp[NoAsms] >>
  disch_then drule_all >> simp[]
QED

Finalise held_eval_direct_selection_mods

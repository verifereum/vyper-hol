(* Static inputs of the array and tuple routes for linked value subscripts. *)
Theory bodySubscriptValueBaseMods
Ancestors
  exprBodyPreProps exprSimHypsDefs loweringPosts placeTypingProps
  exprLowering allocLimits allocLimitsProps supportedExprTraverse
  vyperAST vyperTypeSystem vyperTypeExprResult vyperTypeCallGraph
  vyperTypeCallStackSoundness finite_map integer list

Theorem subscript_base_post_type_mods[local]:
  expr_body_pre_mods mods cenv cx env (Subscript ann obj idx) es ==>
  post_value_type cenv obj = expr_type obj
Proof
  strip_tac >>
  reverse (Cases_on `?t fid args drv. obj = Call t (IntCall fid) args drv`)
  >- (irule post_value_type_not_int_call >> metis_tac[]) >>
  gvs[] >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  `type_place_expr env (Call t (IntCall fid) args drv) = NONE` by
    simp[Once well_typed_expr_def] >>
  drule expr_body_pre_mods_well_typed >>
  simp[Once well_typed_expr_def] >> strip_tac >>
  Cases_on `FLOOKUP env.fn_sigs fid` >>
  gvs[subscript_base_type_exact_def] >>
  drule_all_then assume_tac expr_sim_inv_mods_return_type >>
  simp[expr_type_def, lowered_value_type_def]
QED

Theorem subscript_val_base_cases_mods:
  expr_body_pre_mods mods cenv cx env (Subscript ann obj idx) es /\
  place_type cenv obj = ValPT bt ==>
  bt = expr_type obj /\ post_value_type cenv obj = expr_type obj /\
  ((?et bd. bt = ArrayT et bd) \/ (?tys. bt = TupleT tys))
Proof
  strip_tac >>
  `bt = expr_type obj /\ ((?et bd. bt = ArrayT et bd) \/ (?tys. bt = TupleT tys))`
    suffices_by (drule_then assume_tac subscript_base_post_type_mods >> simp[]) >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  `place_map_tables_agree_on_defined cenv env /\
   (!nsid ty. FLOOKUP env.bare_globals nsid = SOME ty ==>
              cenv.ce_hashmap_info nsid = NONE)` by fs[expr_sim_inv_mods_def] >>
  drule expr_body_pre_mods_well_typed >>
  simp[Once well_typed_expr_def] >> strip_tac
  >- (drule_all_then assume_tac place_type_well_typed_on_defined >>
      Cases_on `expr_type obj` >> gvs[subscript_type_ok_def]) >>
  drule_all_then assume_tac place_type_checked_place_on_defined >>
  Cases_on `vt` >> gvs[value_type_place_def] >>
  drule_then assume_tac type_place_expr_annotation >>
  Cases_on `expr_type obj` >> gvs[subscript_vtype_def]
QED

Theorem subscript_tuple_pre_mods:
  expr_body_pre_mods mods cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = TupleT tys ==>
  expr_body_pre_mods mods cenv cx env obj es /\
  ?ity k. idx = Literal ity (IntL (&k)) /\ k < LENGTH tys /\ ann = EL k tys
Proof
  strip_tac >>
  `well_typed_expr env obj /\ subscript_type_ok (TupleT tys) idx ann` by
    (drule expr_body_pre_mods_well_typed >>
     simp[Once well_typed_expr_def] >> strip_tac >> gvs[] >>
     drule_then assume_tac type_place_expr_vtype_annotation >>
     Cases_on `vt` >> gvs[vtype_annotation_ok_def, subscript_vtype_def]) >>
  reverse conj_tac
  >- (qpat_x_assum `subscript_type_ok _ _ _` mp_tac >>
      simp[subscript_type_ok_tuple] >> strip_tac >>
      rename1 `idx = Literal it (IntL i)` >>
      qexistsl [`it`, `Num i`] >> gvs[INT_OF_NUM]) >>
  `~array_slot_base cenv obj` by
    (strip_tac >> drule array_slot_base_is_ArrayT >> simp[]) >>
  qpat_x_assum `expr_body_pre_mods _ _ _ _ (Subscript _ _ _) _` mp_tac >>
  simp[expr_body_pre_mods_def, byte_widths_expr_def, alloc_limits_expr_def,
       int_calls_expr_def, expr_has_evm_run_thm, EVERY_APPEND,
       Once supported_expr_exists_def] >>
  strip_tac >>
  drule_then assume_tac call_evaluation_safe_append_left >>
  qpat_x_assum `~supported_expr_exists (unallocated_bare_global_root _ _) (Subscript _ _ _)`
    (strip_assume_tac o SIMP_RULE bool_ss [Once supported_expr_exists_def]) >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!target. supported_expr_exists _ (Subscript _ _ _) ==> _` irule >>
  simp[Once supported_expr_exists_def]
QED

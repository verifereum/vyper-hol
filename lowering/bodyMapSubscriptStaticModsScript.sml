(* Static typing of a linked mapping access, before either operand runs. *)
Theory bodyMapSubscriptStaticMods
Ancestors
  bodyFullPredsMods exprBodyPreProps exprSimSubscriptMap exprSimMapDefs
  exprSimHypsDefs placeTypingProps exprLowering vyperTypeSystem vyperTypeExprResult
  vyperTypeInvariants vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperAST vyperState allocLimits
  allocLimitsProps supportedExprTraverse list option

Theorem subscript_vtype_mapping_range[local]:
  subscript_vtype bty ity = SOME (HashMapT ikt ivt) ==>
  ?kt. bty = HashMapT kt (HashMapT ikt ivt) /\ ity = kt /\ hashmap_key_type kt
Proof
  Cases_on `bty`
  >- (rename1 `subscript_vtype (Type ty) _ = _ ==> _` >>
      Cases_on `ty` >> simp[subscript_vtype_def, AllCaseEqs()]) >>
  simp[subscript_vtype_def, AllCaseEqs()]
QED

Theorem map_pre_subscript_typed_mods[local]:
  expr_map_pre_mods mods cenv cx env (Subscript ann obj idx) es ==>
  ?kt ikt ivt.
    type_place_expr env obj = SOME (HashMapT kt (HashMapT ikt ivt)) /\
    expr_type idx = kt /\ hashmap_key_type kt
Proof
  simp[expr_map_pre_mods_def] >> strip_tac >>
  qpat_x_assum `type_place_expr _ (Subscript _ _ _) = _` mp_tac >>
  simp[well_typed_expr_def, AllCaseEqs()] >> strip_tac >>
  drule_then strip_assume_tac subscript_vtype_mapping_range >> gvs[] >>
  metis_tac[]
QED

Theorem map_pre_subscript_base_mods[local]:
  expr_map_pre_mods mods cenv cx env (Subscript ann obj idx) es /\
  type_place_expr env obj = SOME (HashMapT kt vt) ==>
  expr_map_pre_mods mods cenv cx env obj es
Proof
  strip_tac >>
  `~array_slot_base cenv obj` by
    (irule type_place_hashmap_not_array_slot_base >> goal_assum (drule_at Any)) >>
  qpat_x_assum `expr_map_pre_mods _ _ _ _ (Subscript _ _ _) _` mp_tac >>
  simp[expr_map_pre_mods_def, byte_widths_expr_def, alloc_limits_expr_def,
       int_calls_expr_def, expr_has_evm_run_thm, EVERY_APPEND,
       Once supported_expr_exists_def] >>
  strip_tac >> simp[] >> conj_tac
  >- (drule call_evaluation_safe_append_left >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `~supported_expr_exists _ (Subscript _ _ _)` mp_tac >>
      simp[Once supported_expr_exists_def]) >>
  rpt strip_tac >>
  qpat_assum `!target. _ ==> EXISTS _ _` irule >> simp[Once supported_expr_exists_def]
QED

Theorem map_pre_compile_type_mods[local]:
  expr_map_pre_mods mods cenv cx env obj es /\
  type_place_expr env obj = SOME (HashMapT kt vt) ==>
  place_type cenv obj = MapPT kt vt
Proof
  simp[expr_map_pre_mods_def, expr_sim_inv_mods_def] >> strip_tac >>
  drule_all place_type_checked_place_on_defined >> simp[value_type_place_def]
QED

Theorem map_subscript_static_mods:
  (!mods cenv cx env ann obj idx es.
    expr_map_pre_mods mods cenv cx env (Subscript ann obj idx) es ==>
    expr_map_pre_mods mods cenv cx env obj es /\
    ?kt ikt ivt.
      type_place_expr env obj = SOME (HashMapT kt (HashMapT ikt ivt)) /\
      place_type cenv obj = MapPT kt (HashMapT ikt ivt) /\
      expr_type idx = kt /\ hashmap_key_type kt /\
      ~subscript_reads_base cx obj idx /\ ~copies_subscript_base cenv obj idx) /\
  (!mods cenv cx env ann obj idx es kt vt.
    expr_body_pre_mods mods cenv cx env (Subscript ann obj idx) es /\
    place_type cenv obj = MapPT kt vt ==>
    expr_map_pre_mods mods cenv cx env obj es /\
    type_place_expr env obj = SOME (HashMapT kt vt) /\
    vt = Type ann /\ IS_SOME (evaluate_type (get_tenv cx) ann) /\
    expr_type idx = kt /\ hashmap_key_type kt /\
    ~subscript_reads_base cx obj idx /\ ~copies_subscript_base cenv obj idx)
Proof
  conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_then strip_assume_tac map_pre_subscript_typed_mods >>
      drule_all_then assume_tac map_pre_subscript_base_mods >> simp[] >>
      drule_all_then assume_tac map_pre_compile_type_mods >> simp[] >>
      drule map_base_no_overlap >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_all_then assume_tac expr_body_pre_mods_map_subscript_base >>
  `?bkt bvt. type_place_expr env obj = SOME (HashMapT bkt bvt)` by
    fs[expr_map_pre_mods_def] >>
  drule_all_then assume_tac map_pre_compile_type_mods >> gvs[] >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  `~well_typed_expr env obj` by metis_tac[well_typed_expr_not_hashmap_place] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_map_pre_mods_def, expr_sim_inv_mods_def, env_consistent_def,
       env_context_consistent_def] >>
  qpat_x_assum `well_typed_expr _ (Subscript _ _ _)` mp_tac >>
  simp[well_typed_expr_def, subscript_vtype_def, well_formed_type_def] >>
  strip_tac >> gvs[] >> drule map_base_no_overlap >> simp[]
QED

(* Seam 2 joint induction, a frozen leaf of the subscript step: the
   mapping-place producer for a Subscript (the target's second conjunct).
   FROZEN OWNER LEAF: proved by its own run, cheat until then. *)
Theory bodyIntCallFamAggSubscriptMap
Ancestors
  bodyIntCallJointContract bodyIntCallFamAggSubscriptBaseOutcome
  bodyIntCallFamAggSubscriptCompile exprSimSubscriptMap exprSimMapDefs
  placeTypingProps exprSimDefs exprSimHypsDefs exprLowering vyperTypeSystem supportedExprs

Theorem intcall_map_subscript_types:
  expr_map_pre ce cx env (Subscript ann obj idx) es ==>
  ?kt ikt ivt.
    type_place_expr env obj = SOME (HashMapT kt (HashMapT ikt ivt)) /\
    place_type ce obj = MapPT kt (HashMapT ikt ivt)
Proof
  strip_tac >>
  `expr_map_pre ce cx env obj es` by
    (drule_all expr_map_pre_subscript_base >> simp[]) >>
  `?kt vt. type_place_expr env obj = SOME (HashMapT kt vt)` by
    fs[expr_map_pre_def] >>
  `place_map_tables_agree_on_defined ce env` by
    fs[expr_map_pre_def, expr_sim_inv_def] >>
  `place_type ce obj = MapPT kt vt` by
    (drule_all place_type_checked_place_on_defined >> simp[value_type_place_def]) >>
  `?ikt ivt. vt = HashMapT ikt ivt` by
    (qpat_x_assum `expr_map_pre _ _ _ (Subscript _ _ _) _` mp_tac >>
     simp[expr_map_pre_def, Once well_typed_expr_def] >>
     Cases_on `vt` >> simp[subscript_vtype_def, AllCaseEqs()]) >>
  gvs[] >> metis_tac[]
QED

Theorem intcall_map_subscript_support:
  (supported_place_expr tops (Subscript ann obj idx) \/
   supported_effect_place_expr tops (Subscript ann obj idx)) ==>
  (supported_place_expr tops obj \/ supported_effect_place_expr tops obj) /\
  supportedExprs$supported_expr tops idx
Proof
  simp[Once supported_pure_expr_def, Once supported_effect_expr_def,
       supported_expr_def] >> metis_tac[]
QED

Theorem intcall_subscript_map_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?a base idx. e = Subscript a base idx) ==>
  intcall_map_producer fp e
Proof
  strip_tac >> gvs[] >>
  rename1 `Subscript ann obj idx` >>
  `intcall_map_producer fp obj /\ intcall_forced_producer fp idx` by
    (conj_tac
     >- (first_x_assum (qspec_then `obj` mp_tac) >> simp[vyperASTTheory.expr_size_def]) >>
     first_x_assum (qspec_then `idx` mp_tac) >> simp[vyperASTTheory.expr_size_def]) >>
  rewrite_tac[intcall_map_producer_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule intcall_map_subscript_types >> strip_tac >>
  drule intcall_map_subscript_support >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr obj) /\
   calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr idx)` by
    gvs[vyperTypeCallGraphTheory.int_calls_expr_def] >>
  drule_all exprSimMapKeyTheory.compile_expr_mapping_subscript_parts >> strip_tac >>
  irule gas_outcome_conseq >>
  irule_at (Pos last) intcall_mapping_base_outcome >>
  simp[] >>
  qexistsl_tac [`HashMapT ikt ivt`, `ty`, `sp`, `sn`, `sm`, `sb`, `sa`,
                `slot`, `kt`, `key`, `hashed`, `env`, `ce`, `bvv`, `expr_map_res_ok`] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  gvs[vyperHashMapStorageTheory.select_result_hashmap_nested] >>
  drule vyperStoragePlaceProvenanceTheory.storage_mapping_region_step >>
  disch_then (qspec_then `kv` assume_tac) >>
  simp[contextTheory.mk_ptr_def, contextTheory.vv_location_def]
QED

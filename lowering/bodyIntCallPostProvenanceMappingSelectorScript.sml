(* Mapping selectors use the actual storage endpoint of the mapping outcome. *)
Theory bodyIntCallPostProvenanceMappingSelector
Ancestors
  bodyIntCallPostProvenanceOrdinary bodyIntCallProducerInterface
  bodyPtrSubscriptSeamMapPost exprSimSubscriptMap exprSimMapKey
  exprSimMapDefs exprSimDefs loweringPosts context vyperAST
  gasOutcome gasSummaryCompose exprSimHypsDefs vyperTypeSystem
  vyperInterpreter vyperStoragePlaceProvenance vyperState vyperTypeExprResult

Theorem effect_free_mapping_case[local]:
  !e ce nc ctx fn cx.
    acyclic_struct_metadata ce.ce_struct_fields /\ ~expr_has_effect e ==>
    expr_map_case nc ctx fn ce cx e
Proof
  measureInduct_on `expr_size e` >> rpt gen_tac >> strip_tac >>
  Cases_on `e`
  >~ [`TopLevelName _ _`] >- simp[compile_toplevel_map_case]
  >~ [`Subscript _ obj idx`]
  >- (irule compile_subscript_map_map_case >> conj_tac
      >- (rpt strip_tac >> irule (cj 1 ordinary_effect_free_cases) >> gvs[]) >>
      first_x_assum irule >> gvs[expr_size_def]) >>
  irule expr_map_case_other >> simp[]
QED

Theorem intcall_mapping_subscript_outcome:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  ~expr_has_effect (Subscript ann obj idx) /\
  place_type cenv obj = MapPT kt vt /\
  compile_expr cenv ty (Subscript ann obj idx) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (eval_expr cx (Subscript ann obj idx)) expr_vv_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_expr cx (Subscript ann obj idx)) (es,s0)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func cenv cx (Subscript ann obj idx) es sa sb s0 ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      intcall_vv_provenance cenv cx ann sa sb ee tv vv t)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> irule gas_outcome_conseq >>
  irule_at (Pos last) compile_mapping_subscript_outcome >> simp[] >>
  qexistsl_tac [`vv`, `vt`, `ty`, `sb`, `sa`, `F`, `kt`, `env`, `cenv`, `expr_vv_res_ok`] >>
  simp[subscript_result_predicates_exceptions] >> conj_tac
  >- (irule effect_free_mapping_case >> gvs[]) >>
  conj_tac
  >- (rpt strip_tac >> irule (cj 1 ordinary_effect_free_cases) >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `expr_map_pre cenv cx env obj es` by
    (drule_all expr_body_pre_map_subscript_base >> simp[]) >>
  `type_place_expr env obj = SOME (HashMapT kt vt)` by
    (drule_all expr_map_pre_checked_type >> simp[]) >>
  `~copies_subscript_base cenv obj idx` by
    metis_tac[map_base_no_overlap] >>
  `~well_typed_expr env obj` by
    metis_tac[well_typed_expr_not_hashmap_place] >>
  `vt = Type ann` by
    (qpat_x_assum `expr_body_pre _ _ _ (Subscript _ _ _) _` mp_tac >>
     simp[expr_body_pre_def, Once well_typed_expr_def] >>
     Cases_on `vt` >> simp[subscript_vtype_def, AllCaseEqs()]) >>
  `tp = ann` by
    (drule_all compile_expr_mapping_subscript_parts >> strip_tac >> gvs[]) >>
  gvs[] >>
  qpat_x_assum `select_result _ _ _ _ _ = _` mp_tac >>
  simp[select_result_def, extend_place_def, lift_option_type_def,
       lift_option_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  Cases_on `evaluate_type (get_tenv cx) ann` >> gvs[raise_def, return_def] >>
  drule storage_mapping_region_step >> disch_then (qspec_then `kv` assume_tac) >>
  simp[] >> conj_tac
  >- (irule mapping_leaf_vv_post >> gvs[expr_sim_inv_def]) >>
  Cases_on `tr` >> gvs[intcall_vv_provenance_def, slot_loc_def]
QED

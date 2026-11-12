(* Counted mapping subscript outcomes and their value/mapping consumers. *)
Theory bodySubscriptMappingMemory
Ancestors
  bodyMappingOutcomeMemory bodyMappingTailMemory exprSimSubscriptMap
  exprSimMapMemDefs exprSimMemDefs bodyMemoryPreds exprSimMapDefs
  exprSimWordArgs exprSimProps exprLoweringProps loweringPosts
  vyperHashMapStorage vyperTypeSystem exprSimSource placeTypingProps
  vyperStoragePlaceProvenance exprSimHypsDefs exprLowering
  vyperTypeExprResult exprSimMapKey vyperInterpreter vyperState

Theorem compile_mapping_subscript_outcome_mem:
  body_expr_mem_ok cx obj /\
  (!s tv t. eval_expr cx obj s = (INL tv,t) ==> body_expr_mem_ok cx idx) /\
  body_inv tops ctx cenv cx /\
  (expr_body_pre cenv cx env (Subscript ann obj idx) es \/
   expr_map_pre cenv cx env (Subscript ann obj idx) es) /\
  place_type cenv obj = MapPT kt vt /\
  compile_expr cenv ty (Subscript ann obj idx) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible (eval_expr cx (Subscript ann obj idx)) A es /\
  (!ex. A (INR ex) ==> expr_map_res_ok (INR ex)) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (eval_expr cx (Subscript ann obj idx)) (es,s0)
    (\res ee t. ?tr base_slot kv tv tp p.
       res = INL tv /\
       storage_mapping_region cx tr base_slot (HashMapT kt vt) /\
       select_result cx (expr_type obj) (HashMapRef tr base_slot kt vt)
         (ValueSubscript kv) ee = (INL tv,ee) /\
       expr_type idx = kt /\ hashmap_key_type kt /\
       (?key_ty. evaluate_type (get_tenv cx) kt = SOME key_ty /\
                 value_has_type key_ty kv) /\
       expr_sim_inv cenv cx env ee /\ vv = LocatedValue tp p /\
       p.ptr_location = slot_loc tr /\
       eval_operand p.ptr_operand t =
         SOME (hashmap_slot base_slot (encode_hashmap_key kt kv)) /\
       stmt_state_rel ctx func cenv cx ee t /\ wb_frame cenv es ee sa s0 t /\
       (~expr_has_effect (Subscript ann obj idx) ==>
          pure_frame cenv func es sa s0 t) /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  disch_tac >> match_mp_tac compile_mapping_subscript_outcome_mem_given_tail >>
  conj_tac
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC compile_mapping_index_success_tail_mem) >>
  first_assum ACCEPT_TAC
QED

Theorem body_subscript_map_mem:
  body_expr_mem_ok cx obj /\
  (!s tv t. eval_expr cx obj s = (INL tv,t) ==> body_expr_mem_ok cx idx) /\
  body_inv tops ctx cenv cx /\
  expr_map_pre cenv cx env (Subscript ann obj idx) es ==>
  expr_map_sim_mem ctx func cenv cx ty (Subscript ann obj idx) es
Proof
  strip_tac >> rw[expr_map_sim_mem_def] >>
  `expr_map_pre cenv cx env obj es` by
    (drule_all expr_map_pre_subscript_base >> simp[]) >>
  `?kt vt. type_place_expr env obj = SOME (HashMapT kt vt)` by
    fs[expr_map_pre_def] >>
  `place_map_tables_agree_on_defined cenv env` by
    fs[expr_map_pre_def, expr_sim_inv_def] >>
  `place_type cenv obj = MapPT kt vt` by
    (drule_all place_type_checked_place_on_defined >> simp[value_type_place_def]) >>
  irule gas_outcome_conseq >>
  irule_at (Pos last) compile_mapping_subscript_outcome_mem >> simp[] >>
  qexistsl_tac [`vv`, `vt`, `ty`, `tops`] >>
  goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  qexistsl_tac [`kt`, `env`, `expr_map_res_ok`] >>
  simp[] >> conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `?ikt ivt. vt = HashMapT ikt ivt` by
    (qpat_x_assum `expr_map_pre _ _ _ (Subscript _ _ _) _` mp_tac >>
     simp[expr_map_pre_def, Once well_typed_expr_def] >>
     Cases_on `vt` >> simp[subscript_vtype_def, AllCaseEqs()]) >>
  gvs[vyperHashMapStorageTheory.select_result_hashmap_nested] >>
  drule storage_mapping_region_step >> disch_then (qspec_then `kv` assume_tac) >>
  simp[] >>
  qpat_x_assum `wb_frame _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[loweringPostsTheory.wb_frame_def] >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem body_subscript_map_vv_mem:
  body_expr_mem_ok cx obj /\
  (!s tv t. eval_expr cx obj s = (INL tv,t) ==> body_expr_mem_ok cx idx) /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  place_type cenv obj = MapPT kt vt ==>
  expr_vv_sim_mem ctx func cenv cx ty (Subscript ann obj idx) es
Proof
  strip_tac >> rw[expr_vv_sim_mem_def] >>
  irule gas_outcome_conseq >>
  irule_at (Pos last) compile_mapping_subscript_outcome_mem >> simp[] >>
  qexistsl_tac [`vv`, `vt`, `ty`, `tops`] >>
  goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  qexistsl_tac [`kt`, `env`, `expr_vv_res_ok`] >>
  simp[subscript_result_predicates_exceptions] >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `expr_map_pre cenv cx env obj es` by
    (drule_all expr_body_pre_map_subscript_base >> simp[]) >>
  `type_place_expr env obj = SOME (HashMapT kt vt)` by
    (drule_all expr_map_pre_checked_type >> simp[]) >>
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
  `contract_storage_well_formed cx ee /\ storage_layout_safe cx` by
    gvs[expr_sim_inv_def] >>
  drule_all mapping_leaf_storage_valid >> strip_tac >>
  drule_all mapping_leaf_vv_holds >> strip_tac >>
  simp[vv_post_def, vyperASTTheory.expr_type_def, vv_at_def] >>
  qpat_x_assum `wb_frame _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[loweringPostsTheory.wb_frame_def] >>
  strip_tac >> rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC, Cases_on `tr` >> gvs[slot_loc_def, vv_store_bound_nonmem] >> NO_TAC]
QED

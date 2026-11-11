(* Value selection from a mapping: counted sequencing and storage post. *)
Theory bodyIntCallFamAggSubscriptMapValue
Ancestors
  bodyIntCallFamAggSubscriptBaseOutcome bodyIntCallFamAggSubscriptPosts
  bodyIntCallFamAggSubscriptTypedSupport bodyIntCallJointContract
  exprSimSubscriptMap exprSimMapKey exprSimMapDefs exprSimHypsDefs
  supportedExprs supportedExprForms exprLowering vyperTypeSystem
  vyperTypeExprResult vyperTypeCallGraph gasOutcome loweringPosts context

Theorem intcall_subscript_mapping_value_type:
  expr_body_pre ce cx env (Subscript ann obj idx) es /\
  place_type ce obj = MapPT kt vt ==> vt = Type ann
Proof
  strip_tac >>
  `expr_map_pre ce cx env obj es` by
    (drule_all expr_body_pre_map_subscript_base >> simp[]) >>
  `type_place_expr env obj = SOME (HashMapT kt vt)` by
    (drule_all expr_map_pre_checked_type >> simp[]) >>
  `~well_typed_expr env obj` by
    metis_tac[well_typed_expr_not_hashmap_place] >>
  qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
  simp[expr_body_pre_def, Once well_typed_expr_def] >>
  Cases_on `vt` >> simp[subscript_vtype_def, AllCaseEqs()]
QED

Theorem intcall_subscript_mapping_outcome:
  (!e'. expr_size e' < expr_size (Subscript ann obj idx) ==>
     intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
     intcall_map_producer fp e') /\
  place_type ce obj = MapPT kt vt /\
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  expr_body_pre ce fp.jc_cx env (Subscript ann obj idx) es /\
  supported_expr fp.jc_tops (Subscript ann obj idx) /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr (Subscript ann obj idx)) /\
  compile_expr ce ty (Subscript ann obj idx) sa = (vv,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  gas_admissible (eval_expr fp.jc_cx (Subscript ann obj idx)) expr_vv_res_ok es /\
  intcall_expr_res fp ce env es sa s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_expr fp.jc_cx (Subscript ann obj idx)) (es,s)
    (\res ee u. ?tv. res = INL tv /\
      vv_holds ce fp.jc_cx (post_value_type ce (Subscript ann obj idx)) tv vv ee u /\
      vv_at ce fp.jc_cx (post_value_type ce (Subscript ann obj idx)) sa sb ee tv vv u /\
      (post_value_type ce (Subscript ann obj idx) <> expr_type (Subscript ann obj idx) ==>
        vv_own ce fp.jc_cx (post_value_type ce (Subscript ann obj idx)) sa sb ee tv vv u) /\
      (~expr_has_effect (Subscript ann obj idx) ==> vv_storage_live fp.jc_cx vv ee u) /\
      (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
      (post_value_type ce (Subscript ann obj idx) <> NoneT /\
       ~is_word_type (post_value_type ce (Subscript ann obj idx)) /\
       ~is_bytestring_type (post_value_type ce (Subscript ann obj idx)) /\
       (case vv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
       !tv'. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce (Subscript ann obj idx)) = SOME tv' ==>
        ?w a k. eval_operand (vv_operand vv) u = SOME w /\
          a <= w2n w /\ w2n w + type_memory_size tv' <= a + k /\
          a + k < dimword (:256) /\
          (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a + k <= b + z)) /\
      intcall_expr_cont fp ce env es sa s ee sb u)
    (\res ee r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `vt = Type ann` by (drule_all intcall_subscript_mapping_value_type >> simp[]) >>
  gvs[] >>
  drule_all compile_expr_mapping_subscript_parts >> strip_tac >>
  `intcall_map_producer fp obj /\ intcall_forced_producer fp idx` by
    (conj_tac
     >- (first_x_assum (qspec_then `obj` mp_tac) >> simp[vyperASTTheory.expr_size_def]) >>
     first_x_assum (qspec_then `idx` mp_tac) >> simp[vyperASTTheory.expr_size_def]) >>
  `supported_expr fp.jc_tops idx` by (drule supported_subscript_index >> simp[]) >>
  Q.SUBGOAL_THEN
    `supported_place_expr fp.jc_tops obj \/ supported_effect_place_expr fp.jc_tops obj`
    assume_tac
  >- fs[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def] >>
  `calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr obj) /\
   calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr idx)` by
    fs[vyperTypeCallGraphTheory.int_calls_expr_def,
       vyperTypeCallStackSoundnessTheory.calls_follow_call_graph_append] >>
  Q.SUBGOAL_THEN
    `expr_body_pre ce fp.jc_cx env (Subscript ann obj idx) es \/
     expr_map_pre ce fp.jc_cx env (Subscript ann obj idx) es` assume_tac
  >- simp[] >>
  `!ex. expr_vv_res_ok (INR ex) ==> expr_map_res_ok (INR ex)` by
    simp[subscript_result_predicates_exceptions] >>
  drule_all intcall_mapping_base_outcome >>
  disch_then (mp_then Any irule gas_outcome_conseq) >> simp[] >>
  rpt gen_tac >> strip_tac >>
  gvs[] >>
  rename1 `intcall_expr_cont fp ce env es sa s ee sb u` >>
  rename1 `select_result _ _ (HashMapRef tr base_slot kt _) (ValueSubscript kv) ee = (INL selected,ee)` >>
  `vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx (Subscript ann obj idx)
     es sa sb s ee selected (LocatedValue ann (mk_ptr slot (slot_loc tr))) u` by
    (irule intcall_mapping_leaf_post >> simp[mk_ptr_def] >> metis_tac[]) >>
  fs[vv_post_def, vv_operand_def, mk_ptr_def, vv_location_def] >>
  Cases_on `tr` >> gvs[slot_loc_def]
QED

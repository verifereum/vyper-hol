(* Storage and nested-mapping endpoint posts, independent of sequencing. *)
Theory bodyIntCallFamAggSubscriptPosts
Ancestors
  bodyIntCallJointContract exprSimSubscriptMap loweringPosts exprSimHypsDefs
  exprSimDefs vyperHashMapStorage vyperState vyperInterpreter
  vyperAST compileEnv venomState vyperStoragePlaceProvenance

Theorem intcall_mapping_leaf_post:
  storage_mapping_region fp.jc_cx tr slot (HashMapT kt (Type ann)) /\
  select_result fp.jc_cx (expr_type obj)
    (HashMapRef tr slot kt (Type ann)) (ValueSubscript kv) ee =
    (INL selected,ee) /\
  p.ptr_location = slot_loc tr /\
  eval_operand p.ptr_operand u =
    SOME (hashmap_slot slot (encode_hashmap_key kt kv)) /\
  intcall_expr_cont fp ce env es sa s0 ee sb u ==>
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx (Subscript ann obj idx)
    es sa sb s0 ee selected (LocatedValue ann p) u
Proof
  strip_tac >>
  qpat_x_assum `select_result _ _ _ _ _ = _` mp_tac >>
  simp[select_result_def, extend_place_def, lift_option_type_def,
       lift_option_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  Cases_on `evaluate_type (get_tenv fp.jc_cx) ann` >>
  gvs[raise_def, return_def] >>
  drule storage_mapping_region_step >>
  disch_then (qspec_then `kv` assume_tac) >>
  `contract_storage_well_formed fp.jc_cx ee /\
   storage_layout_safe fp.jc_cx /\
   stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee u` by
    fs[intcall_expr_cont_def, intcall_joint_res_def, expr_sim_inv_def] >>
  drule_all mapping_leaf_storage_valid >> strip_tac >>
  drule_all mapping_leaf_vv_holds >> strip_tac >>
  simp[vv_post_def, expr_type_def, vv_at_def] >>
  conj_tac >- (Cases_on `tr` >> gvs[slot_loc_def]) >>
  fs[intcall_expr_cont_def] >>
  Cases_on `tr` >> gvs[slot_loc_def] >> gvs[]
QED

Theorem intcall_mapping_nested_post:
  storage_mapping_region fp.jc_cx tr slot (HashMapT kt (HashMapT ikt ivt)) /\
  select_result fp.jc_cx (expr_type obj)
    (HashMapRef tr slot kt (HashMapT ikt ivt)) (ValueSubscript kv) ee =
    (INL selected,ee) /\
  p.ptr_location = slot_loc tr /\
  eval_operand p.ptr_operand u =
    SOME (hashmap_slot slot (encode_hashmap_key kt kv)) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\
  intcall_expr_cont fp ce env es sa s0 ee sb u ==>
  ?slot'. selected = HashMapRef tr slot' ikt ivt /\
    storage_mapping_region fp.jc_cx tr slot' (HashMapT ikt ivt) /\
    eval_operand p.ptr_operand u = SOME slot' /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\
    intcall_expr_cont fp ce env es sa s0 ee sb u
Proof
  strip_tac >>
  gvs[select_result_hashmap_nested] >>
  drule storage_mapping_region_step >>
  disch_then (qspec_then `kv` assume_tac) >> simp[]
QED

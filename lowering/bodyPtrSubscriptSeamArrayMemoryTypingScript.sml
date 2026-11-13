Theory bodyPtrSubscriptSeamArrayMemoryTyping
Ancestors
  bodySim exprSimHypsDefs vyperAST vyperTypeSystem placeTypingProps
  compileEnv loweringPosts exprSimHyps exprLowering valueEncoding list
  exprSimSubscriptArraySource exprSimSource

Theorem array_subscript_index_type:
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd ==>
  ann = et /\ is_int_type (expr_type idx)
Proof
  simp[expr_body_pre_def, Once well_typed_expr_def] >> strip_tac >>
  gvs[subscript_type_ok_def] >>
  drule type_place_expr_vtype_annotation >> strip_tac >>
  Cases_on `vt` >> gvs[vtype_annotation_ok_def, subscript_vtype_def, AllCaseEqs()]
QED

Theorem array_subscript_memory_layout:
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et (Fixed n) /\
  evaluate_type (get_tenv cx) et = SOME etv ==>
  ann = et /\ is_int_type (expr_type idx) /\
  type_memory_bytes cenv (ArrayT et (Fixed n)) =
    type_memory_size (ArrayTV etv (Fixed n)) /\
  elem_size_in_location cenv LocMemory et = type_memory_size etv /\
  type_memory_bytes cenv (lowered_value_type cenv (Subscript ann obj idx)) =
    type_memory_size etv /\
  post_value_type cenv (Subscript ann obj idx) = et
Proof
  strip_tac >> drule_all array_subscript_index_type >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env obj es` by
    metis_tac[expr_body_pre_array_subscript_base] >>
  `IS_SOME (evaluate_type (get_tenv cx) (expr_type obj))` by
    metis_tac[expr_body_pre_type_evaluates] >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes cenv ty = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  simp[lowered_value_type_def, post_value_type_def, expr_type_def,
       elem_size_in_location_def, is_slot_addressed_def] >>
  first_x_assum irule >> gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()]
QED

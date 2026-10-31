(* Source typing determines the run-time ABI projection shape. *)
Theory vyperTypeAbiProjectionSoundness
Ancestors
  vyperInterpreter vyperTypeStatePreservation vyperTypeExprResult
  vyperTypeValues vyperTypeSystem vyperAbiProjectionTyping
  list rich_list option vyperAST vyperState vyperValue vyperTypeExprSoundness
  vyperTyping vyperPlaceStatePreservation vyperPlaceResultTyping
  vyperValueOperation vyperAssignPreservesType vyperAbiOperand vyperAbiExprTyping vyperAbiReadTyping
  vyperTypeAbiPlaceSoundness

Theorem abi_subscript_source_shape:
  subscript_type_ok ct ie ty /\ subscript_index_matches ct ie index /\
  value_runtime_typed env (expr_type ie) index /\
  evaluate_type env.type_defs ct = SOME parent ==>
  ?child. evaluate_type env.type_defs ty = SOME child /\
          abi_projection_shape parent (ValueSubscript index) child
Proof
  strip_tac >>
  `is_int_type (expr_type ie)` by
    (Cases_on `ct` >> fs[subscript_type_ok_tuple] >>
     gvs[subscript_type_ok_def, AllCaseEqs(), expr_type_def]) >>
  `?i. index = IntV i` by
    (gvs[value_runtime_typed_def] >> drule_all int_typed_value_is_IntV >> simp[]) >>
  gvs[] >> Cases_on `ct` >> fs[subscript_type_ok_tuple] >>
  gvs[subscript_type_ok_def, subscript_index_matches_def, AllCaseEqs()]
  >- (drule evaluate_type_TupleT_cases >> strip_tac >>
      gvs[LIST_REL_EL_EQN, abi_projection_shape_def, oEL_THM] >> metis_tac[]) >>
  gvs[Once evaluate_type_def, AllCaseEqs(), abi_projection_shape_def]
QED

Theorem abi_snapshot_subscript_sound:
  abi_projection_shape parent (ValueSubscript index) child /\
  value_has_type parent v /\ well_formed_type_value parent ==>
  (!err. evaluate_subscripts parent v [ValueSubscript index] = INR err ==>
    !msg. err <> TypeError msg) /\
  (!w. evaluate_subscripts parent v [ValueSubscript index] = INL w ==>
    value_has_type child w)
Proof
  Cases_on `parent` >> Cases_on `index` >> simp[abi_projection_shape_def] >>
  rpt strip_tac >> gvs[] >> FIRST [
    (rename1 `value_has_type (ArrayTV child bound) v` >>
     `?av. v = ArrayV av` by (Cases_on `v` >> gvs[value_has_type_def]) >> gvs[] >>
     Cases_on `array_index (ArrayTV child bound) av i` >>
     gvs[evaluate_subscripts_def] >>
     metis_tac[array_index_has_type, well_formed_type_value_def]),
    (rename1 `oEL (Num i) tvs = SOME child` >>
     `subscripts_type (TupleTV tvs) [ValueSubscript (IntV i)] = SOME child` by
       gvs[subscripts_type_def, subscript_type_def, oEL_THM] >>
     metis_tac[evaluate_subscripts_type, evaluate_subscripts_typed_error])]
QED

Theorem abi_subscript_sound:
  env.type_defs = get_tenv cx /\ abi_operand_valid st parent arg /\
  evaluate_type env.type_defs ct = SOME parent /\
  subscript_type_ok ct ie ty /\ subscript_index_matches ct ie index /\
  value_runtime_typed env (expr_type ie) index /\
  subscript_abi_operand cx parent arg index st = (res,rt) ==>
  rt = st /\ no_type_error_result res /\
  case res of INL child => ?tv. evaluate_type env.type_defs ty = SOME tv /\
                              abi_operand_valid rt tv child
            | INR _ => T
Proof
  strip_tac >> drule_all abi_subscript_source_shape >> strip_tac >>
  `well_formed_type_value child` by metis_tac[evaluate_type_well_formed_type_value] >>
  Cases_on `?v. arg = AbiSnapshot v`
  >- (gvs[abi_operand_valid_def] >>
      drule_all abi_snapshot_subscript_sound >> strip_tac >>
      Cases_on `evaluate_subscripts parent v [ValueSubscript index]` >>
      gvs[subscript_abi_operand_def, bind_def, lift_sum_def, return_def, raise_def,
          no_type_error_result_def, abi_operand_valid_def] >> metis_tac[]) >>
  `subscript_abi_operand cx parent arg index st =
     project_abi_operand cx arg (ValueSubscript index) st` by
    (Cases_on `arg` >> gvs[subscript_abi_operand_def]) >>
  fs[] >> drule_all (SRULE [] abi_projection_valid) >> strip_tac >>
  Cases_on `res` >> gvs[]
QED

Theorem abi_subscript_place_sound:
  env.type_defs = get_tenv cx /\ abi_place_result_valid env st arg vt /\
  well_formed_vtype env.type_defs vt /\ vtype_annotation_ok vt ct /\
  subscript_vtype vt (expr_type ie) = SOME vt' /\
  value_runtime_typed env (expr_type ie) index /\
  evaluate_type env.type_defs ct = SOME parent /\
  subscript_abi_operand cx parent arg index st = (res,rt) ==>
  rt = st /\ no_type_error_result res /\
  case res of INL child => abi_place_result_valid env rt child vt' | INR _ => T
Proof
  strip_tac >> Cases_on `vt`
  >- (rename1 `abi_place_result_valid env st arg (Type t)` >> Cases_on `t` >>
      gvs[subscript_vtype_def, vtype_annotation_ok_def,
          abi_place_result_valid_def, AllCaseEqs()] >>
      rename1 `evaluate_type (get_tenv cx) (ArrayT elem_ty bd) = SOME parent` >>
      `subscript_type_ok (ArrayT elem_ty bd) ie elem_ty` by simp[subscript_type_ok_def] >>
      `subscript_index_matches (ArrayT elem_ty bd) ie index` by simp[subscript_index_matches_def] >>
      qpat_assum `env.type_defs = get_tenv cx`
        (fn th => drule_all (SRULE [th] (SPEC_ALL abi_subscript_sound))) >>
      simp[subscript_type_ok_def, subscript_index_matches_def, abi_place_result_valid_def]) >>
  gvs[abi_place_result_valid_def, vtype_annotation_ok_def,
      subscript_vtype_def, AllCaseEqs()] >>
  rename1 `well_formed_vtype (get_tenv cx) (HashMapT (expr_type ie) result_vt)` >>
  Cases_on `result_vt` >>
  gvs[well_formed_vtype_def, well_formed_type_def, IS_SOME_EXISTS,
      subscript_abi_operand_def, project_abi_operand_def,
      lift_option_type_def, bind_def, return_def,
      abi_place_result_valid_def, abi_operand_valid_def, no_type_error_result_def] >>
  metis_tac[evaluate_type_well_formed_type_value]
QED

Theorem abi_attribute_sound:
  abi_expr_result_valid env st e arg /\
  attribute_type env.type_defs (expr_type e) id = SOME ty /\
  attribute_abi_operand cx arg id st = (res,rt) ==>
  rt = st /\ no_type_error_result res /\
  case res of INL child => abi_expr_result_valid env rt (Attribute ty e id) child | INR _ => T
Proof
  simp[abi_expr_result_valid_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `expr_type e` >> gvs[attribute_type_def, evaluate_type_def, AllCaseEqs()] >>
  rename1 `FLOOKUP env.type_defs sid = SOME (StructArgs fields)` >>
  `?child_tv. evaluate_type env.type_defs ty = SOME child_tv /\
      ALOOKUP (ZIP (MAP FST fields,tvs)) id = SOME child_tv` by
    (irule attribute_type_evaluates >>
     qexists_tac `StructT sid` >> simp[attribute_type_def, evaluate_type_def]) >>
  `well_formed_type_value child_tv` by metis_tac[evaluate_type_well_formed_type_value] >>
  Cases_on `?v. arg = AbiSnapshot v`
  >- (gvs[abi_operand_valid_def] >>
      `subscripts_type (StructTV (ZIP (MAP FST fields,tvs))) [AttrSubscript id] = SOME child_tv` by
        simp[subscripts_type_def, subscript_type_def] >>
      Cases_on `evaluate_attribute v id` >>
      gvs[attribute_abi_operand_def, lift_sum_def, return_def, raise_def, bind_def,
          no_type_error_result_def, expr_type_def, abi_operand_valid_def]
      >- (irule vyperPlaceStatePreservationTheory.evaluate_subscripts_type >>
          goal_assum (drule_at Any) >> qexists_tac `v` >> simp[] >>
          Cases_on `v` >> gvs[evaluate_attribute_def, evaluate_subscripts_def, AllCaseEqs()]) >>
      `?values. v = StructV values` by (Cases_on `v` >> gvs[value_has_type_def]) >>
      gvs[] >>
      `evaluate_subscripts (StructTV (ZIP (MAP FST fields,tvs))) (StructV values)
         [AttrSubscript id] = INR (TypeError "evaluate_subscripts AttrSubscript")` by
        gvs[evaluate_attribute_def, evaluate_subscripts_def, AllCaseEqs()] >>
      metis_tac[evaluate_subscripts_typed_error]) >>
  `attribute_abi_operand cx arg id st = project_abi_operand cx arg (AttrSubscript id) st` by
    (Cases_on `arg` >> gvs[attribute_abi_operand_def]) >>
  fs[] >> drule_all (SRULE [] abi_struct_projection_valid) >> strip_tac >>
  Cases_on `res` >> gvs[expr_type_def]
QED

Theorem abi_place_annotation_evaluates:
  abi_place_result_valid env st arg vt /\ vtype_annotation_ok vt ct ==>
  ?tv. evaluate_type env.type_defs ct = SOME tv
Proof
  Cases_on `vt` >> simp[abi_place_result_valid_def, vtype_annotation_ok_def,
                       evaluate_type_def] >> metis_tac[]
QED

Theorem abi_pop_pointer_valid:
  abi_operand_valid st (ArrayTV tv (Dynamic n)) arg /\
  (~?v. arg = AbiSnapshot v) /\ abi_pop_pointer cx arg st = (res,rt) ==>
  rt = st /\ no_type_error_result res /\
  case res of INL child => abi_operand_valid rt tv child | INR _ => T
Proof
  strip_tac >>
  `well_formed_type_value tv` by
    (Cases_on `arg` >> gvs[abi_operand_valid_def, well_formed_type_value_def]) >>
  qpat_x_assum `abi_pop_pointer _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[abi_pop_pointer_def, bind_def] >>
  Cases_on `read_abi_operand cx arg st` >>
  rename1 `read_abi_operand cx arg st = (read_res,read_st)` >>
  drule_all read_abi_operand_valid >> strip_tac >> gvs[] >> Cases_on `read_res` >> gvs[]
  >- (drule_all read_abi_operand_valid_typed >> strip_tac >>
      rename1 `value_has_type (ArrayTV tv (Dynamic n)) value` >>
      Cases_on `value` >> gvs[value_has_type_def] >>
      rename1 `read_abi_operand cx arg st = (INL (ArrayV array),st)` >>
      Cases_on `array` >> gvs[value_has_type_def] >>
      rename1 `read_abi_operand cx arg st = (INL (ArrayV (DynArrayV vs)),st)` >>
      Cases_on `vs` >>
      simp[check_def, assert_def, ignore_bind_def, bind_def, return_def,
           raise_def, no_type_error_result_def] >>
      strip_tac >> drule_all (SRULE [] abi_array_projection_valid) >>
      simp[no_type_error_result_def]) >>
  strip_tac >> gvs[no_type_error_result_def]
QED

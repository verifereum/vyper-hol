(* General source selection, including historical and non-memory places. *)
Theory bodyPtrSubscriptSeamTupleSource
Ancestors
  bodyPtrSubscriptSeamTuplePost bodyPtrSubscriptTupleDispatch
  exprSimTuple exprSimSource exprSimDefs exprSimHypsDefs
  bodyPtrAttributeSource loweringPosts exprLowering exprSimAttributeProps
  vyperAST vyperValue vyperTyping vyperTypeSystem vyperTypeABI
  vyperInterpreter vyperState vyperValueOperation vyperTypeDefaults
  list

Theorem tuple_selected_source:
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = TupleT tys /\ post_value_type cenv obj = TupleT tys /\
  eval_expr cx obj es = (INL btv,es1) /\
  vv_post ctx func cenv cx obj es sa sb s0 es1 btv bvv q ==>
  ?ity k tvs vs tv'.
    idx = Literal ity (IntL (&k)) /\ ann = EL k tys /\ k < LENGTH tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
    LENGTH tvs = LENGTH tys /\ LENGTH vs = LENGTH tvs /\
    values_have_types tvs vs /\
    read_result cx btv es1 = (INL (ArrayV (TupleV vs)),es1) /\
    select_result cx (TupleT tys) btv (ValueSubscript (IntV (&k))) es1 = (INL tv',es1) /\
    read_result cx tv' es1 = (INL (EL k vs),es1)
Proof
  strip_tac >> drule_all tuple_subscript_pre >> strip_tac >> gvs[] >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >> gvs[] >>
  `?v w. read_result cx btv es1 = (INL v,es1) /\
    eval_operand (vv_operand bvv) q = SOME w` by
    (irule attribute_vv_holds_read_operand >> fs[vv_post_def] >> metis_tac[]) >>
  `value_has_type tvt v` by metis_tac[] >>
  gvs[Once evaluate_type_def, evaluate_types_OPT_MMAP, AllCaseEqs()] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  rename1 `values_have_types tvs vs` >>
  `LENGTH tvs = LENGTH tys /\ LENGTH vs = LENGTH tvs` by
    metis_tac[OPT_MMAP_LENGTH, values_have_types_length] >>
  `~popped_at_elem btv k es1` by
    (drule_all tuple_popped_clash_unreachable >>
     simp[tuple_popped_clash_def, literal_int_index_def] >> metis_tac[]) >>
  Cases_on `select_result cx (TupleT tys) btv (ValueSubscript (IntV (&k))) es1` >>
  rename1 `_ = (res,es2)` >>
  `!m. res <> INR (Error (TypeError m))` by
    (`eval_expr cx (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) es =
      (res,es2)` by simp[tuple_subscript_source, bind_def] >>
     qpat_x_assum `expr_body_pre _ _ _ obj _` kall_tac >>
     drule_all expr_body_pre_vv_res_ok >> simp[expr_vv_res_ok_def] >>
     strip_tac >> gvs[]) >>
  metis_tac[select_tuple_read]
QED

Theorem tuple_selection_gas_obs:
  select_result cx ty tv (ValueSubscript (IntV i)) ee = (r,ee) ==>
  select_result cx ty tv (ValueSubscript (IntV i)) (ee with gas_obs := tail) =
    (r,ee with gas_obs := tail)
Proof
  Cases_on `tv`
  >~ [`Value v`]
  >- (simp[select_result_def, bind_def, lift_option_type_def, lift_sum_def,
           return_def, raise_def] >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]))
  >~ [`HashMapRef tr slot kt vt`]
  >- (Cases_on `vt` >>
      simp[select_result_def, extend_place_def, bind_def,
           lift_option_type_def, return_def, raise_def, LET_THM] >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def])) >>
  rename1 `PlaceR pl` >> Cases_on `pl`
  >~ [`StoragePlace tr slot ptv`]
  >- (Cases_on `ptv` >> Cases_on `tr` >>
      simp[select_result_def, extend_place_def, extend_storage_place_def,
           resolve_array_element_def, vyperStoragePlaceProvenanceTheory.resolve_array_element_empty,
           check_def, assert_def, ignore_bind_def, get_storage_backend_def,
           get_accounts_def, get_transient_storage_def, bind_def,
           lift_option_type_def, return_def, raise_def, pairTheory.UNCURRY,
           LET_THM] >>
      rpt (BasicProvers.FULL_CASE_TAC >>
           gvs[check_def, assert_def, ignore_bind_def,
               get_storage_backend_def, get_accounts_def,
               get_transient_storage_def, bind_def, return_def, raise_def,
               pairTheory.UNCURRY])) >>
  simp[select_result_def, extend_place_def, place_type_value_def,
       read_place_def, get_scopes_def, get_immutables_def,
       get_address_immutables_def, bind_def, ignore_bind_def,
       lift_option_type_def, lift_sum_def, return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[bind_def, return_def, raise_def])
QED

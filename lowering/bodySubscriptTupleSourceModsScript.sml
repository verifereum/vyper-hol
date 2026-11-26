(* Source-side tuple selection at the reached base state, before the ADD. *)
Theory bodySubscriptTupleSourceMods
Ancestors
  exprSimTuple exprSimSubscriptArraySource bodyAttributeReadOperandMods
  bodyFullPostsMods bodySimStmtFacts exprBodyPreProps exprBodyPreCallSafetyProps
  exprSimSource exprSimHypsDefs vyperTypeSoundness vyperTypeABI vyperTypeCallGraph
  vyperPlaceTyping vyperTypeExprSoundness vyperTypeInvariants vyperTyping
  vyperValue vyperMisc vyperTypeEvalCaseProofs vyperState list rich_list pair
Libs monadsyntax

Theorem tuple_linked_typed_eval[local]:
  expr_sim_inv_mods mods cenv cx env es /\ well_typed_expr env e /\
  call_evaluation_safe cx (int_calls_expr e) /\ eval_expr cx e es = (res,ee) ==>
  no_type_error_result res /\
  (case res of INL raw => eval_result_typed (env,cx,ee) raw (Type (expr_type e))
             | INR _ => T)
Proof
  simp[expr_sim_inv_mods_def] >> strip_tac >>
  drule_all_then strip_assume_tac typed_expr_evaluation_sound >> simp[]
QED

Theorem tuple_no_popped_cell[local]:
  popped_keys_indexed ee.scopes /\ env.type_defs = get_tenv cx /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  eval_result_typed (env,cx,ee) raw (Type (TupleT tys)) ==>
  ~popped_at_elem raw k ee
Proof
  strip_tac >> Cases_on `raw` >> gvs[popped_at_elem_def] >>
  rename1 `PlaceR p` >> Cases_on `p` >> gvs[popped_at_elem_def] >>
  gvs[eval_result_typed_def, runtime_place_typed_memory] >>
  rename1 `subscripts_type entry.type path = SOME (TupleTV tvs)` >>
  drule_all_then mp_tac lookup_scopes_popped_keys_indexed >>
  simp[EVERY_MEM, MEM_MAP] >> strip_tac >> rpt strip_tac >>
  qpat_x_assum `!key. _ ==> _` (qspec_then `path ++ [ValueSubscript (IntV (&k))]` mp_tac) >>
  (impl_tac >- (goal_assum (drule_at (Pat `MEM _ _`)) >> simp[])) >>
  simp[APPEND_11_LENGTH]
QED

Theorem tuple_value_components[local]:
  evaluate_type (get_tenv cx) (TupleT tys) = SOME tv /\ value_has_type tv v ==>
  ?tvs vs. evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
           OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
           LENGTH tvs = LENGTH tys /\ LENGTH vs = LENGTH tvs /\
           v = ArrayV (TupleV vs) /\ values_have_types tvs vs
Proof
  rw[Once evaluate_type_def, AllCaseEqs()] >>
  gvs[evaluate_types_OPT_MMAP] >>
  drule_then assume_tac OPT_MMAP_LENGTH >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >>
  gvs[value_has_type_def] >>
  drule values_have_types_length >> simp[] >>
  simp[Once evaluate_type_def, evaluate_types_OPT_MMAP]
QED

Theorem tuple_subscript_selected_source_mods:
  idx = Literal ity (IntL (&k)) /\ ann = EL k tys /\ k < LENGTH tys /\
  well_typed_expr env (Subscript ann obj idx) /\
  expr_body_pre_mods mods cenv cx env obj (es with gas_obs := gs) /\
  expr_type obj = TupleT tys /\ post_value_type cenv obj = TupleT tys /\
  eval_expr cx obj (es with gas_obs := gs) = (INL btv,ee) /\
  vv_post_mods H ctx func cenv cx obj es sa sb s0 ee btv bvv q ==>
  ?tvs vs tv'.
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
    LENGTH tvs = LENGTH tys /\ LENGTH vs = LENGTH tvs /\ values_have_types tvs vs /\
    eval_result_typed (env,cx,ee) btv (Type (TupleT tys)) /\
    read_result cx btv ee = (INL (ArrayV (TupleV vs)),ee) /\
    select_result cx (TupleT tys) btv (ValueSubscript (IntV (&k))) ee = (INL tv',ee) /\
    read_result cx tv' ee = (INL (EL k vs),ee)
Proof
  strip_tac >> gvs[] >>
  `vv_holds_mods cenv cx (TupleT tys) btv bvv ee q` by
    (qhdtm_assum `vv_post_mods` (mp_tac o REWRITE_RULE [vv_post_mods_def]) >> simp[]) >>
  drule_then strip_assume_tac attribute_read_operand_mods >>
  `bind (eval_expr cx obj) (read_result cx) (es with gas_obs := gs) = (INL v,ee)` by
    simp[bind_def] >>
  drule_all_then strip_assume_tac (REWRITE_RULE [ETA_THM] expr_body_pre_eval_mods) >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `?tv. evaluate_type (get_tenv cx) (TupleT tys) = SOME tv /\ value_has_type tv v` by
    (first_x_assum (qspec_then `v` mp_tac) >> simp[value_runtime_typed_def]) >>
  drule_all_then strip_assume_tac tuple_value_components >> gvs[] >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  `eval_result_typed (env,cx,ee) btv (Type (TupleT tys))` by
    (drule_all_then strip_assume_tac tuple_linked_typed_eval >> gvs[]) >>
  `~popped_at_elem btv k ee` by
    (irule tuple_no_popped_cell >> conj_tac
     >- fs[expr_sim_inv_mods_def] >>
     qexistsl_tac [`cx`,`env`,`tvs`,`tys`] >> simp[]) >>
  Cases_on `select_result cx (TupleT tys) btv (ValueSubscript (IntV (&k))) ee` >>
  rename1 `select_result _ _ _ _ _ = (res,ef)` >>
  `eval_expr cx (Subscript (EL k tys) obj (Literal ity (IntL (&k))))
      (es with gas_obs := gs) = (res,ef)` by simp[tuple_source, bind_def] >>
  `!m. res <> INR (Error (TypeError m))` by
    (`call_evaluation_safe cx (int_calls_expr (Subscript (EL k tys) obj (Literal ity (IntL (&k)))))` by
       simp[int_calls_expr_def] >>
     qpat_x_assum `eval_expr cx obj _ = _` kall_tac >>
     drule_all_then strip_assume_tac tuple_linked_typed_eval >>
     fs[no_type_error_result_def]) >>
  `k < LENGTH vs` by simp[] >>
  drule_all_then strip_assume_tac select_tuple_read >> gvs[]
QED

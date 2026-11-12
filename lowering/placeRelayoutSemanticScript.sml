(* Semantic layout and invariant boundary, independent of compiler states. *)
Theory placeRelayoutSemantic
Ancestors
  bodyPlacePremises placeRelayoutBounds placeRelayoutRawSource
  bodySimAugPlaceLoad annassignRelayoutSource assignRelayoutCaller
  exprSimSource exprSimHyps vyperStoragePlaceProvenance typedMemoryCopy
  vyperTypeArgFits vyperTypeInvariants exprSimHypsDefs
  exprSimIfExpCompat vyperTypeSystem vyperAST compileEnv

Theorem arg_type_fits_source_assignable[local]:
  (!t u. arg_type_fits t u ==>
    !tenv. assignable_type tenv u /\ well_formed_type tenv t ==>
      assignable_type tenv t) /\
  (!ts us. arg_types_fit ts us ==>
    !tenv. EVERY (assignable_type tenv) us /\ EVERY (well_formed_type tenv) ts ==>
      EVERY (assignable_type tenv) ts)
Proof
  ho_match_mp_tac arg_type_fits_ind >> rw[arg_type_fits_def] >>
  gvs[assignable_type_def] >>
  all_tac
  >>~- ([`assignable_type tenv t`],
     first_x_assum irule >> simp[] >>
     gvs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
     drule vyperTypeValuesTheory.evaluate_type_ArrayT_cases >>
     metis_tac[]) >>
  `EVERY (well_formed_type tenv) ts` by
    (gvs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
     drule vyperTypeValuesTheory.evaluate_type_TupleT_cases >> strip_tac >>
     gvs[listTheory.EVERY_MEM, listTheory.LIST_REL_EL_EQN,
         listTheory.MEM_EL] >>
     metis_tac[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  metis_tac[arg_types_fit_LENGTH, listTheory.LENGTH_NIL]
QED

Theorem strict_widened_assignment_nonword:
  expr_body_pre cenv cx env e es /\
  type_widens_to env.type_defs (expr_type e) dty /\
  ~(lowered_value_type cenv e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type cenv e) /\
    arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
  ~is_word_type dty
Proof
  strip_tac >>
  drule expr_body_pre_var_types_well_formed >> strip_tac >>
  `well_typed_expr env e /\
   sfields_tenv_consistent cenv.ce_struct_fields env.type_defs` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  drule ifexp_lowered_type_classify >>
  disch_then (qspec_then `cenv` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >> gvs[] >>
  drule ifexp_body_pre_intcall_physical >> strip_tac >>
  strip_tac >>
  `expr_type (Call ty (IntCall fid) args drv) = dty` by
    metis_tac[compileEnvTheory.type_widens_to_word] >>
  `well_formed_type env.type_defs
     (expr_type (Call ty (IntCall fid) args drv))` by
    metis_tac[exprSafeOperandTheory.well_typed_expr_type_well_formed] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  `type_widens_to (get_tenv cx)
    (lowered_value_type cenv (Call ty (IntCall fid) args drv)) ty` by
    fs[type_widens_to_def, expr_type_def] >>
  metis_tac[compileEnvTheory.type_widens_to_word, expr_type_def]
QED

Theorem widened_place_semantic_endpoint:
  expr_body_pre cenv cx env e es /\
  supported_expr tops e /\ supported_program tops /\
  cenv.ce_func_return_type = build_func_return_type tops /\
  get_module_code cx NONE = SOME tops /\
  type_widens_to env.type_defs (expr_type e) dty /\
  assignable_type env.type_defs (expr_type e) /\
  target_indices_pre cenv cx env bt /\
  ~(lowered_value_type cenv e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type cenv e) /\
    arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
  eval_expr cx e (es with gas_obs := gs) = (INL (Value v),mid) /\
  eval_target_place cx bt mid = (INL p,ee) ==>
  expr_sim_inv cenv cx env ee /\ storage_place_region cx p /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  ~is_word_type (lowered_value_type cenv e) /\
  ~is_bytestring_type (lowered_value_type cenv e) /\
  post_value_type cenv e = lowered_value_type cenv e /\
  lowered_value_type cenv e <> expr_type e /\
  lowered_value_type cenv e <> dty /\
  type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty /\
  assignable_type (get_tenv cx) (lowered_value_type cenv e) /\
  ?stv dtv.
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv /\
    type_memory_bytes cenv (lowered_value_type cenv e) < dimword (:256)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~is_word_type dty` by metis_tac[strict_widened_assignment_nonword] >>
  drule_all assign_relayout_source_classify >> strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  `expr_sim_inv cenv cx env mid` by
    metis_tac[exprSimSourceTheory.expr_body_pre_eval_result] >>
  `expr_sim_inv cenv cx env ee` by metis_tac[aug_place_target_inv] >>
  `storage_place_region cx p` by metis_tac[eval_target_place_region] >>
  `(do r <- eval_expr cx e; read_result cx r od)
    (es with gas_obs := gs) = (INL v,mid)` by
    simp[vyperStateTheory.bind_def, vyperStateTheory.read_result_def,
         vyperStateTheory.return_def] >>
  `value_runtime_typed env dty v` by
    metis_tac[memoryLocalRhsPropsTheory.memory_rhs_read_destination_typed] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  fs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
  `type_widens_to env.type_defs (expr_type e) dty` by metis_tac[] >>
  drule_all annassign_relayout_read_layout >> strip_tac >>
  `~is_word_type (expr_type e)` by metis_tac[return_source_word_widens_eq] >>
  drule_all expr_body_pre_relayout_source_bound >> strip_tac >>
  `assignable_type (get_tenv cx) (lowered_value_type cenv e)` by
    (irule (cj 1 arg_type_fits_source_assignable) >>
     reverse conj_tac
     >- simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
     qexists_tac `expr_type e` >> simp[] >>
     fs[type_widens_to_def] >> gvs[]) >>
  simp[] >> metis_tac[]
QED

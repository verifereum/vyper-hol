(* Source read and logical indices for ordinary linked array membership. *)
Theory bodyMembershipArrayReadMods
Ancestors
  bodyFullPostsMods bodyCopyReadPhysicalTypeMods bodySimStmtFacts bodyWriteSubscriptSourceMods
  exprBodyPreProps exprSimHyps exprSimBopRestWordBasics exprSimBopRestWordCompose
  exprSimBopRestWordIndex exprSimBopRestWordLoads exprSimAttribute exprSimMemorySource
  abiEncodeArgsSim vyperTypeEvalCaseProofs vyperTypeSystem vyperTyping vyperArray
  vyperValue vyperValueOperation vyperState vyperTypeExprSoundness vyperAST vyperTypeValues
  loweringPosts exprSimHypsDefs list words
Libs monadsyntax

Theorem membership_read_suffix[local]:
  vv_holds_mods ce cx ty raw vv fin u ==>
  ?v. !tail. read_result cx raw (fin with gas_obs := tail) =
      (INL v,fin with gas_obs := tail)
Proof
  Cases_on `vv` >> simp[vv_holds_mods_def]
  >- (strip_tac >> drule rest_word_vv_read_suffix >> simp[]) >>
  rename1 `p.ptr_location = LocCode` >> Cases_on `p.ptr_location = LocCode`
  >- (simp[immutable_holds_mods_def] >> strip_tac >>
      drule immutable_holds_read >> strip_tac >>
      drule read_result_gas_obs >> metis_tac[]) >>
  simp[] >> strip_tac >> drule rest_word_vv_read_suffix >> simp[]
QED

Theorem membership_array_fits[local]:
  arg_type_fits ty (ArrayT ety bd) /\ is_word_type ety ==>
  ?pbd. ty = ArrayT ety pbd /\
        (case bd of Fixed n => pbd = Fixed n | Dynamic n => ?m. pbd = Dynamic m)
Proof
  Cases_on `ty` >> simp[arg_type_fits_def] >>
  rename1 `arg_type_fits (ArrayT t b) (ArrayT ety bd)` >>
  Cases_on `b` >> Cases_on `bd` >> simp[arg_type_fits_def] >>
  metis_tac[abi_args_word_fits_eq]
QED

Theorem membership_post_fits[local]:
  expr_body_pre_mods mods ce cx env e es ==>
  arg_type_fits (post_value_type ce e) (expr_type e)
Proof
  strip_tac >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    (irule copy_lowered_fits_mods >> qexistsl [`cx`,`env`,`es`,`mods`] >>
     fs[expr_body_pre_mods_def]) >>
  Cases_on `?ty fid args drv. e = Call ty (IntCall fid) args drv` >>
  gvs[post_value_type_def,expr_type_def] >> IF_CASES_TAC >> simp[]
QED

Theorem membership_indexed_words[local]:
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME et /\
  value_has_type et needle /\ value_has_type (ArrayTV et bd) (ArrayV av) ==>
  (evaluate_in_array (ArrayTV et bd) needle av <=>
   MEM (typed_val_to_w256 et needle)
      (GENLIST (\i. typed_val_to_w256 et
         (THE (array_index (ArrayTV et bd) av (&i))))
        (array_length (ArrayTV et bd) av)))
Proof
  strip_tac >>
  `!i. i < array_length (ArrayTV et bd) av ==>
     array_index (ArrayTV et bd) av (&i) =
       SOME (THE (array_index (ArrayTV et bd) av (&i)))` by
    (rpt strip_tac >>
     `valid_index (ArrayTV et bd) av (&i)` by simp[valid_index_def] >>
     drule array_index_valid >>
     Cases_on `array_index (ArrayTV et bd) av (&i)` >> simp[]) >>
  drule_all rest_word_array_word_membership >>
  simp[MEM_GENLIST] >> metis_tac[optionTheory.THE_DEF]
QED

Theorem membership_read_annotation[local]:
  expr_body_pre_mods mods ce cx env e es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) ==>
  ?rt. evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\ value_has_type rt v
Proof
  strip_tac >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := gs)` by
    simp[write_subscript_source_gas_obs_mods] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_eval_mods) >> strip_tac >>
  drule_then (assume_tac o MATCH_MP expr_sim_inv_mods_env) expr_body_pre_mods_inv >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  fs[value_runtime_typed_def]
QED

Theorem membership_evaluate_array[local]:
  evaluate_type tenv ety = SOME et /\ t = ArrayT ety bd /\
  evaluate_type tenv t = SOME tv ==> tv = ArrayTV et bd
Proof
  metis_tac[evaluate_type_ArrayT_cases, optionTheory.SOME_11]
QED

Theorem membership_array_read_mods:
  is_word_type (expr_type e1) /\ expr_type e2 = ArrayT (expr_type e1) bd /\
  expr_body_pre_mods mods ce cx env e1 es /\
  expr_body_pre_mods mods ce cx env e2 mid /\
  (!tail. bind (eval_expr cx e1) (read_result cx) (es with gas_obs := obs1 ++ tail) =
     (INL needle,mid with gas_obs := tail)) /\
  (!tail. eval_expr cx e2 (mid with gas_obs := obs2 ++ tail) =
     (INL raw,fin with gas_obs := tail)) /\
  vv_holds_mods ce cx (post_value_type ce e2) raw vv (fin with gas_obs := []) u ==>
  ?et pbd av ws.
    post_value_type ce e2 = ArrayT (expr_type e1) pbd /\
    (case bd of Fixed n => pbd = Fixed n | Dynamic n => ?m. pbd = Dynamic m) /\
    (case bd of Fixed n => n | Dynamic n => n) < dimword (:256) /\
    evaluate_type (get_tenv cx) (expr_type e1) = SOME et /\
    evaluate_type (get_tenv cx) (post_value_type ce e2) = SOME (ArrayTV et pbd) /\
    value_has_type (ArrayTV et bd) (ArrayV av) /\
    value_has_type (ArrayTV et pbd) (ArrayV av) /\ value_has_type et needle /\
    (!tail. read_result cx raw (fin with gas_obs := tail) =
       (INL (ArrayV av),fin with gas_obs := tail)) /\
    ws = GENLIST (\i. typed_val_to_w256 et
      (THE (array_index (ArrayTV et bd) av (&i))))
      (array_length (ArrayTV et bd) av) /\
    (evaluate_in_array (ArrayTV et bd) needle av <=> MEM (typed_val_to_w256 et needle) ws) /\
    (case bd of Fixed n => LENGTH ws = n | Dynamic n => LENGTH ws <= n)
Proof
  strip_tac >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` (assume_tac o SRULE [APPEND_NIL])) >>
  drule_at (Pat `bind _ _ _ = _`) membership_read_annotation >>
  disch_then (drule_then (qx_choose_then `et` strip_assume_tac)) >>
  `?pbd. post_value_type ce e2 = ArrayT (expr_type e1) pbd /\
        (case bd of Fixed n => pbd = Fixed n | Dynamic n => ?m. pbd = Dynamic m)` by
    (irule membership_array_fits >> simp[] >>
     qpat_assum `expr_body_pre_mods _ _ _ _ e2 _` (mp_tac o MATCH_MP membership_post_fits) >>
     simp[]) >>
  drule membership_read_suffix >>
  disch_then (qx_choose_then `v` (assume_tac o SRULE [evaluation_state_fupdfupds])) >>
  `bind (eval_expr cx e2) (read_result cx) (mid with gas_obs := obs2) =
     (INL v,fin with gas_obs := [])` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` (assume_tac o SRULE [APPEND_NIL])) >>
     simp[bind_def]) >>
  drule_at (Pat `bind (eval_expr _ e2) _ _ = _`) membership_read_annotation >>
  disch_then (drule_then strip_assume_tac) >>
  `rt = ArrayTV et bd` by metis_tac[membership_evaluate_array] >>
  gvs[] >>
  `?av. v = ArrayV av` by (Cases_on `v` >> fs[value_has_type_def]) >>
  gvs[] >>
  `~is_word_type (expr_type e2)` by simp[compileEnvTheory.is_word_type_def] >>
  `?pt. evaluate_type (get_tenv cx) (post_value_type ce e2) = SOME pt /\
        value_has_type pt (ArrayV av)` by
    (drule_all copy_read_physical_type_gas_obs_mods >> metis_tac[]) >>
  rename1 `evaluate_type _ (post_value_type ce e2) = SOME pt` >>
  `pt = ArrayTV et pbd` by metis_tac[membership_evaluate_array] >>
  gvs[] >>
  `type_alloc_ok ce (ArrayT (expr_type e1) bd)` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ e2 _`
       (strip_assume_tac o REWRITE_RULE [expr_body_pre_mods_def]) >>
     drule alloc_limits_expr_type_alloc_ok >> simp[]) >>
  drule_all_then assume_tac rest_word_array_alloc_bound >> simp[] >>
  conj_tac
  >- (irule membership_indexed_words >> simp[] >> qexistsl [`cx`,`expr_type e1`] >> simp[]) >>
  Cases_on `bd` >> Cases_on `av` >> gvs[value_has_type_def, array_length_def]
QED

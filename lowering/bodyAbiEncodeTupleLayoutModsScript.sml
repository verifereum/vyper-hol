(* Source layout at the actual wrapped argument-list landing. *)
Theory bodyAbiEncodeTupleLayoutMods
Ancestors
  bodyTypeBuiltinAbiMods bodyCopyReadPhysicalTypeMods bodyCopyArgReadTypesMods
  bodyFullExtCallDirectLayout exprSimAbiEncodeRuntimeInputs
  exprBodyPreProps exprBodyPreTypingProps exprBodyPreCallSafetyProps
  exprSimHypsDefs exprSimAbiEncodeArgsPhysicalCapacity abiEncodeArgsCase
  abiBuiltinEncodeSource abiTypeBoundProps abiDecoderMembers
  typedMemoryCopy entryDecodeStaticProps aggregateEvaluatedLayout
  logArgumentTypes logArgumentTypeEval allocLimits compileEnv exprLowering context
  vyperTypeEvalCaseProofs vyperTypeExprSoundness vyperTypeSystem vyperTypeABI
  vyperTypeArgFits vyperTypeCallGraph vyperABI exprSimHyps
  vyperState vyperContext vyperInterpreter vyperAST list arithmetic

Theorem tuple_eval_types_mods[local]:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  eval_exprs cx args (es with gas_obs := gs) = (INL vs,ee) ==>
  LENGTH args = LENGTH vs /\
  !i. i < LENGTH args ==>
    ?tv ftv. evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
      evaluate_type (get_tenv cx) (expr_type (EL i args)) = SOME ftv /\
      value_has_type tv (EL i vs) /\ value_has_type ftv (EL i vs)
Proof
  strip_tac >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  `(expr_sim_inv_mods mods ce cx env (es with gas_obs := gs) <=>
     expr_sim_inv_mods mods ce cx env es)` by
    simp_tac (srw_ss()) [expr_sim_inv_mods_def] >>
  `expr_sim_inv_mods mods ce cx env (es with gas_obs := gs)` by simp[] >>
  `runtime_consistent env cx (es with gas_obs := gs)` by
    (qpat_x_assum `runtime_consistent _ _ es` mp_tac >>
     simp[runtime_consistent_def, vyperTypeInvariantsTheory.env_consistent_def]) >>
  `env.type_defs = get_tenv cx` by
    (drule_then assume_tac expr_sim_inv_mods_env >>
     drule env_consistent_type_defs_get_tenv >> simp[]) >>
  `well_typed_exprs env args /\ call_evaluation_safe cx (int_calls_exprs args)` by
    (conj_tac >- fs[Once well_typed_expr_def] >>
     drule expr_body_pre_mods_call_evaluation_safe >> simp[int_calls_expr_def]) >>
  `exprs_runtime_typed env args vs` by
    (drule_all abi_encode_eval_exprs_runtime_typed >> simp[]) >>
  `LIST_REL (\e v. value_runtime_typed env (lowered_value_type ce e) v) args vs` by
    (irule copy_arg_read_types_from_members_mods >>
     goal_assum (drule_at Any) >> qexists_tac `ee` >> simp[] >> conj_tac
     >- (rpt strip_tac >>
         `expr_body_pre_mods mods ce cx env e s` by
           metis_tac[type_builtin_body_arg_pre_mods] >>
         irule copy_read_lowered_type_mods >>
         qpat_x_assum `expr_body_pre_mods _ _ _ _ e s` mp_tac >>
         simp[expr_body_pre_mods_def] >> metis_tac[]) >>
     simp[EVERY_MEM] >> rpt strip_tac >>
     drule_all type_builtin_body_arg_pre_mods >> simp[expr_body_pre_mods_def]) >>
  qpat_x_assum `exprs_runtime_typed _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [exprs_runtime_typed_def, LIST_REL_EL_EQN]) >>
  qpat_x_assum `LIST_REL _ args vs`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [LIST_REL_EL_EQN, value_runtime_typed_def]) >>
  conj_tac >- simp[] >> gen_tac >> disch_tac >>
  `i < LENGTH tvs` by decide_tac >>
  qpat_assum `!j. j < LENGTH args ==> ?tv. _` (drule_then strip_assume_tac) >>
  qexistsl_tac [`tv`,`EL i tvs`] >> simp[] >> metis_tac[]
QED

Theorem tuple_row_layout_mods[local]:
  expr_body_pre_mods mods ce cx env e es /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ftv ==>
  arg_type_fits (lowered_value_type ce e) (expr_type e) /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
  type_memory_size tv < 2 ** 64
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  conj_asm1_tac >- (irule copy_lowered_fits_mods >> metis_tac[]) >>
  `!ty rt. evaluate_type (get_tenv cx) ty = SOME rt ==>
      type_memory_bytes ce ty = type_memory_size rt` by
    (rpt strip_tac >> irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >>
     fs[expr_sim_inv_mods_def] >> metis_tac[]) >>
  conj_asm1_tac >- simp[] >>
  Cases_on `is_word_type (expr_type e)`
  >- (`is_word_type (lowered_value_type ce e)` by
        (drule arg_type_fits_word_type >> simp[]) >>
      `type_memory_bytes ce (lowered_value_type ce e) = 32` by
        (irule (cj 3 word_type_dec_sizes) >> simp[]) >>
      qpat_assum `_ = type_memory_size tv` (SUBST1_TAC o SYM) >> simp[]) >>
  `alloc_limits_expr ce e` by fs[expr_body_pre_mods_def] >>
  drule alloc_limits_expr_type_alloc_ok >> simp[type_alloc_ok_def] >> strip_tac >>
  drule (cj 1 abi_args_fits_memory_bytes) >>
  disch_then (qspec_then `ce` mp_tac) >> simp[] >> decide_tac
QED

Theorem tuple_indexed_layout_mods[local]:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  eval_exprs cx args (es with gas_obs := gs) = (INL vs,ee) ==>
  LENGTH args = LENGTH vs /\
  !i. i < LENGTH args ==>
    let t = lowered_value_type ce (EL i args); u = expr_type (EL i args) in
    ?tv ftv. evaluate_type (get_tenv cx) t = SOME tv /\
      evaluate_type (get_tenv cx) u = SOME ftv /\
      arg_type_fits t u /\ value_has_type tv (EL i vs) /\ value_has_type ftv (EL i vs) /\
      type_memory_bytes ce t = type_memory_size tv /\ type_memory_size tv < 2 ** 64
Proof
  strip_tac >> drule_all tuple_eval_types_mods >> strip_tac >> simp[] >>
  gen_tac >> disch_tac >> `i < LENGTH args` by decide_tac >>
  first_x_assum drule >> strip_tac >>
  `expr_body_pre_mods mods ce cx env (EL i args) es` by
    (drule_then assume_tac expr_body_pre_mods_inv >>
     drule type_builtin_body_arg_pre_mods >> simp[EL_MEM]) >>
  drule_all tuple_row_layout_mods >> strip_tac >>
  qexistsl_tac [`tv`,`ftv`] >> asm_rewrite_tac[] >> fs[]
QED

Theorem tuple_source_result_ok_mods[local]:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  ~(LENGTH args = 1 /\ ~ensure) ==>
  target = TupleT (MAP expr_type args) /\ ~(~ensure /\ LENGTH args <= 1) /\
  ?limit. ann = BaseT (BytesT (Dynamic limit)) /\
    vyper_abi_size_bound (get_tenv cx) (TupleT (MAP expr_type args)) +
      abi_encode_method_id_size mid <= limit
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  drule expr_body_pre_mods_well_typed >>
  simp[Once well_typed_expr_def, type_builtin_result_ok_def,
       well_typed_type_builtin_args_def, abi_encode_size_ok_def] >>
  strip_tac >> gvs[abi_encode_source_argument_type] >>
  Cases_on `args` >> gvs[] >> rename1 `well_typed_exprs env (h::t)` >>
  Cases_on `t` >> gvs[]
QED

Theorem tuple_declared_codec[local]:
  LENGTH tys = LENGTH declared /\ sfields_tenv_consistent sf tenv /\
  (!i. i < LENGTH tys ==>
    ?tv ftv. evaluate_type tenv (EL i tys) = SOME tv /\
      evaluate_type tenv (EL i declared) = SOME ftv /\ arg_type_fits (EL i tys) (EL i declared)) /\
  vyper_to_abi_list tenv tys vs = SOME avs ==>
  vyper_to_abi_types tenv declared = vyper_to_abi_types tenv tys /\
  vyper_to_abi_list tenv declared vs = SOME avs /\
  abi_size_bound sf (TupleT tys) <= vyper_abi_size_bound tenv (TupleT declared)
Proof
  strip_tac >>
  `arg_types_fit tys declared` by
    (simp[arg_types_fit_LIST_REL, LIST_REL_EL_EQN] >> metis_tac[]) >>
  `?tvs. LIST_REL (\t tv. evaluate_type tenv t = SOME tv) tys tvs` by
    (qexists_tac `MAP (THE o evaluate_type tenv) tys` >>
     simp[LIST_REL_EL_EQN,EL_MAP] >> rpt strip_tac >>
     `n < LENGTH tys` by decide_tac >>
     first_x_assum drule >> simp[] >> metis_tac[optionTheory.THE_DEF]) >>
  `?ftvs. LIST_REL (\t tv. evaluate_type tenv t = SOME tv) declared ftvs` by
    (qexists_tac `MAP (THE o evaluate_type tenv) declared` >>
     simp[LIST_REL_EL_EQN,EL_MAP] >> rpt strip_tac >>
     `n < LENGTH tys` by decide_tac >>
     first_x_assum drule >> simp[] >> metis_tac[optionTheory.THE_DEF]) >>
  conj_tac >- metis_tac[cj 2 abi_args_fits_abi_type] >>
  conj_tac >- metis_tac[cj 2 abi_args_fits_conversion] >>
  `abi_size_bound sf (TupleT declared) = vyper_abi_size_bound tenv (TupleT declared)` by
    (irule abi_size_bound_tuple_typed >> simp[EVERY_EL] >>
     fs[optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
  pop_assum (SUBST1_TAC o SYM) >> irule (cj 2 abi_args_fits_size_bound) >> simp[]
QED

Theorem abi_encode_tuple_layout_mods:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  ~(LENGTH args = 1 /\ ~ensure) /\
  eval_exprs cx args (es with gas_obs := gs) = (INL vs,ee) /\
  LENGTH (svs:vyper_value list) = LENGTH args ==>
  let tys = MAP (lowered_value_type ce) args;
      declared = MAP expr_type args;
      rows = ZIP (svs,tys) in
  LENGTH vs = LENGTH args /\
  (!i. i < LENGTH tys ==>
    ?tv ftv. evaluate_type (get_tenv cx) (EL i tys) = SOME tv /\
      evaluate_type (get_tenv cx) (EL i declared) = SOME ftv /\
      arg_type_fits (EL i tys) (EL i declared) /\
      value_has_type tv (EL i vs) /\ value_has_type ftv (EL i vs) /\
      type_memory_bytes ce (EL i tys) = type_memory_size tv /\ type_memory_size tv < 2 ** 64) /\
  ?avs ats bytes limit.
    ats = vyper_to_abi_types (get_tenv cx) tys /\
    vyper_to_abi_list (get_tenv cx) tys vs = SOME avs /\
    bytes = enc (Tuple ats) (ListV avs) /\
    LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
      abi_member_head_size at) rows ats /\
    LIST_REL abi_encoder_layout_valid ats avs /\
    LENGTH bytes <= abi_size_bound ce.ce_struct_fields (TupleT tys) /\
    evaluate_type_builtin cx (AbiEncode ensure mid) target declared vs =
      INL (BytesV (abi_encode_method_id_bytes mid ++ bytes)) /\
    ann = BaseT (BytesT (Dynamic limit)) /\
    LENGTH (abi_encode_method_id_bytes mid ++ bytes) <= limit
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >>
  qabbrev_tac `tys = MAP (lowered_value_type ce) args` >>
  qabbrev_tac `declared = MAP expr_type args` >>
  drule_all tuple_indexed_layout_mods >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  conj_asm1_tac
  >- (simp_tac (srw_ss()) [Abbr `tys`, Abbr `declared`, EL_MAP] >>
      qpat_assum `!i. i < LENGTH args ==> ?tv ftv. _`
        (mp_tac o SIMP_RULE (srw_ss()) []) >> simp_tac bool_ss []) >>
  `LENGTH tys = LENGTH declared /\ LENGTH tys = LENGTH vs /\ LENGTH tys = LENGTH svs` by
    simp[Abbr `tys`, Abbr `declared`] >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by
    (drule expr_body_pre_mods_inv >> simp[expr_sim_inv_mods_def]) >>
  `?avs ats bytes.
    vyper_to_abi_list (get_tenv cx) tys vs = SOME avs /\
    ats = vyper_to_abi_types (get_tenv cx) tys /\ bytes = enc (Tuple ats) (ListV avs) /\
    LENGTH bytes <= abi_size_bound ce.ce_struct_fields (TupleT tys) /\
    LIST_REL abi_encoder_layout_valid ats avs /\
    LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
      abi_member_head_size at) (ZIP (svs,tys)) ats` by
    (`LENGTH tys = LENGTH declared /\ LENGTH tys = LENGTH vs /\
       LENGTH tys = LENGTH svs /\ sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
       (!i. i < LENGTH tys ==>
         ?tv ftv. evaluate_type (get_tenv cx) (EL i tys) = SOME tv /\
           evaluate_type (get_tenv cx) (EL i declared) = SOME ftv /\
           arg_type_fits (EL i tys) (EL i declared) /\
           value_has_type tv (EL i vs) /\ value_has_type ftv (EL i vs))`
     suffices_by (disch_then (mp_tac o MATCH_MP extcall_direct_args_layout) >> metis_tac[]) >>
     rpt conj_tac >- decide_tac >- decide_tac >- decide_tac
     >- first_assum ACCEPT_TAC >>
     gen_tac >> disch_tac >>
     qpat_assum `!i. i < LENGTH tys ==> ?tv ftv. _` (drule_then strip_assume_tac) >>
     qexistsl_tac [`tv`,`ftv`] >> asm_rewrite_tac[]) >>
  `vyper_to_abi_types (get_tenv cx) declared = ats /\
   vyper_to_abi_list (get_tenv cx) declared vs = SOME avs /\
   abi_size_bound ce.ce_struct_fields (TupleT tys) <=
     vyper_abi_size_bound (get_tenv cx) (TupleT declared)` by
    (qpat_assum `ats = _` SUBST1_TAC >>
     irule tuple_declared_codec >> asm_rewrite_tac[] >>
     reverse conj_tac >- decide_tac >>
     gen_tac >> disch_tac >> `i < LENGTH tys` by decide_tac >>
     qpat_assum `!i. i < LENGTH tys ==> ?tv ftv. _` (drule_then strip_assume_tac) >>
     qexistsl_tac [`tv`,`ftv`] >> asm_rewrite_tac[]) >>
  `target = TupleT declared /\ ~(~ensure /\ LENGTH declared <= 1) /\
   ?limit. ann = BaseT (BytesT (Dynamic limit)) /\
     vyper_abi_size_bound (get_tenv cx) (TupleT declared) +
       abi_encode_method_id_size mid <= limit` by
    (drule_all tuple_source_result_ok_mods >> simp[Abbr `declared`]) >>
  `evaluate_type_builtin cx (AbiEncode ensure mid) target declared vs =
     INL (BytesV (abi_encode_method_id_bytes mid ++ bytes))` by
    (qpat_assum `target = _` SUBST1_TAC >>
     qpat_assum `bytes = _` SUBST1_TAC >>
     qpat_assum `vyper_to_abi_types _ declared = ats` (SUBST1_TAC o SYM) >>
     irule (PURE_REWRITE_RULE [vyper_to_abi_type_def] abi_builtin_encode_source_tuple) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     simp[Once vyper_to_abi_def]) >>
  `LENGTH (abi_encode_method_id_bytes mid ++ bytes) <= limit` by
    (qpat_assum `_ + abi_encode_method_id_size mid <= limit`
       (assume_tac o REWRITE_RULE [abi_encode_method_id_size_def]) >>
     rewrite_tac[LENGTH_APPEND] >> decide_tac) >>
  qexistsl_tac [`avs`,`limit`] >>
  qpat_x_assum `ats = vyper_to_abi_types _ tys` (SUBST1_TAC o SYM) >>
  qpat_x_assum `bytes = enc _ _` (SUBST1_TAC o SYM) >> asm_rewrite_tac[]
QED

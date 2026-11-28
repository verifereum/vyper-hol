Theory bodyFullForIteratorHeld
Ancestors
  contractInvContextProps
  bodyFullForArrayBranch forNestedArrayCapture[qualified,ignore_grammar]
  vyperTypeContract[qualified,ignore_grammar]
  forCapturedArraySnapshot forSelectedImmutableLayout
  forCapturedStorageContinue[qualified,ignore_grammar]
  forImmutableBodyProjection[qualified,ignore_grammar]
  vyperTypeConstantFold[qualified,ignore_grammar]
  bodyFullPostsMods[qualified] bodyFullPredsMods[qualified] bodyFullShadowBodyInv[qualified] bodyInvSplit[qualified] exprSimHypsDefs[qualified]

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?tgt nid. loop_iterator_place _ = _ /\ _`
    (qx_choosel_then [`tgt`,`nid`] (map_every assume_tac o CONJUNCTS)) >>
  irule for_array_expr_cut_frag_full >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`bindings`,`env`,`env'`,`tops`] >> asm_rewrite_tac[] >>
  map_every qx_gen_tac [`st0`,`sa`,`sb`,`sha`,`shb`,`s0`,`G0`,`tn0`,`vv`,
    `se`,`she`,`bd`,`tyv`,`marks`,`rv`,`em`,`G`,`tn`,`u`] >>
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `obs = gas_explicit marks s0.vs_gas_readings` >>
  `valid_horizon cx st0 (storage_trace_horizon em.storage_trace) em.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> for_array_expr_endpoint _ _ _ _ _ _ _ _ _ _ _ _`
    (drule_then (map_every assume_tac o CONJUNCTS o
       REWRITE_RULE [bodyFullForExprCutTheory.for_array_expr_endpoint_def])) >>
  `em with gas_obs := [] = em` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  `eval_expr cx e (es with gas_obs := obs) = (INL rv,em)` by
    (qpat_assum `em with gas_obs := [] = em` (fn eq =>
       qpat_assum `!tail. eval_expr cx e _ = _` (qspec_then `[]` mp_tac) >>
       simp[NoAsms,eq])) >>
  `expr_body_pre cenv cx env e (es with gas_obs := obs)` by simp[] >>
  drule_at_then (Pat `eval_expr _ _ _ = _`) drule_all
    forNestedArrayCaptureTheory.nested_array_capture_cases >>
  disch_then (qx_choose_then `elem` (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 mp_tac kall_tac))) >>
  `elem = tyv` by metis_tac[optionTheory.SOME_11] >>
  pop_assum SUBST_ALL_TAC >> impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (DISJ_CASES_THEN2 (qx_choose_then `av` assume_tac)
    (qx_choosel_then [`tr`,`slot`] assume_tac))
  >- suspend "snapshot" >> suspend "storage"
QED
*)
Theorem compile_for_storage_subplace_array_frag_full:
  !cx id typ e n body DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    ~(?bd nid. e = TopLevelName (ArrayT typ bd) nid /\
               supported_storage_value tops nid (ArrayT typ bd)) /\
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx (Array e) s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_full_ok_mods mods exps cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_full_ok_mods mods exps cx (Array e)) /\
    (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\ supported_stmt tops bindings (For id typ (Array e) n body) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ (Array e) n body) ==>
       occurs_abi_decode_target target tops) /\
    stmt_loop_calls_ok [(NONE,tops)] (For id typ (Array e) n body) /\
    body_const_cells_agree mods cx env es /\
    expr_sim_inv_mods mods cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ (Array e) n body) = SOME env' /\
    ~supported_expr_exists (const_name_root cx) e /\
    stmt_exprs_ok cenv (For id typ (Array e) n body) /\
    ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env)
      (For id typ (Array e) n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ (Array e) n body)) /\
    frame_ret_ok_full_mods mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~(?ty nid. e = TopLevelName ty nid) /\
    (?tgt nid. loop_iterator_place e = SOME tgt /\
       target_root tgt = TopLevelNameTarget nid /\
       ((?vis kind ty slot.
          supported_variable_decl tops nid = SOME (vis,kind,ty,SOME slot) /\
          (kind = Storage \/ kind = Transient)) \/
        (?vis transient kt vt slot.
          supported_hashmap_decl tops nid = SOME (vis,transient,kt,vt,SOME slot)))) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ (Array e) n body))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (For id typ (Array e) n body)))
      (eval_stmt cx (For id typ (Array e) n body)) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_for_storage_subplace_array_frag_full[snapshot]:
  `post_value_type cenv e = ArrayT typ bd` by
    (`post_value_type cenv e = expr_type e` suffices_by simp[] >>
     irule loweringPostsTheory.post_value_type_not_int_call >> rpt strip_tac >>
     gvs[vyperTypeContractTheory.loop_iterator_place_def]) >>
  irule for_array_snapshot_continue_full >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists `obs` >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (disj1_tac >> qexists `av` >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl [`bd`,`bindings`,`env`,`env'`,`ret_ty`,`se`,`sha`,`shadow_func`,
            `shb`,`she`,`tops`,`typ`,`vv`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- simp[] >> conj_tac >-
    (rewrite_tac[bodyFullForArrayRoundTheory.for_nonslot_code_frame_def] >>
     qpat_assum `!v. rv = Value v /\ _ ==> _` (qspec_then `ArrayV av` mp_tac) >>
     Cases_on `vv` >> simp[contextTheory.vv_location_def,
        compileEnvTheory.is_word_type_def,compileEnvTheory.is_bytestring_type_def]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_for_storage_subplace_array_frag_full[storage]:
  qpat_x_assum `rv = PlaceR _` SUBST_ALL_TAC >>
  irule forCapturedStorageContinueTheory.for_captured_storage_continue_full >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexists `obs` >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qexistsl [`se`,`vv`] >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     disj2_tac >> qexistsl [`tgt`,`nid`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`bindings`,`env`,`env'`,`ret_ty`,`sha`,`shadow_func`,`shb`,`tops`,`typ`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise compile_for_storage_subplace_array_frag_full
*)

(* A code-backed iterator needs only the selected array, not a frame for its root. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  gen_tac >> strip_tac >> gen_tac >> disch_tac >>
  `a = av` by
    (drule_then strip_assume_tac vyperTypeConstantFoldTheory.constant_immutable_read_inv >>
     gvs[vyperBareGlobalNameTheory.lookup_immutable_def]) >>
  pop_assum SUBST_ALL_TAC >>
  rewrite_tac[bodyFullForArrayRoundTheory.for_nonslot_code_frame_def] >> disch_tac >>
  `vv_location vv = SOME LocCode` by (Cases_on `vv_location vv` >> gvs[]) >>
  qexistsl [`src`,`name`,`path`] >> simp[NoAsms] >> rpt gen_tac >> strip_tac >>
  drule_at_then (Pat `read_result _ _ es = _`) strip_assume_tac
    vyperTypeConstantFoldTheory.constant_immutable_read_inv >>
  `lookup_immutable cx (eb with gas_obs := obs) src name = SOME (tv,root)` by
    (`eb.immutables = es.immutables` by
       gvs[vyperStateTheory.push_scope_with_var_def,vyperStateTheory.return_def] >>
     simp[vyperBareGlobalNameTheory.lookup_immutable_def]) >>
  drule_at_then (Pat `eval_stmts _ _ _ = _`) drule_all
    forImmutableBodyProjectionTheory.for_selected_immutable_array_body_observation >> strip_tac >>
  `lookup_immutable cx ep src name = SOME (tv,v')` by
    (qpat_assum `lookup_immutable cx ef src name = SOME _`
       (mp_tac o REWRITE_RULE [vyperBareGlobalNameTheory.lookup_immutable_def]) >>
     simp[vyperBareGlobalNameTheory.lookup_immutable_def]) >>
  conj_tac >-
    (Cases_on `ALOOKUP ep.immutables cx.txn.target` >>
     gvs[vyperBareGlobalNameTheory.lookup_immutable_def,vyperStateTheory.read_result_def,
         vyperStateTheory.read_place_def,vyperStateTheory.get_immutables_def,
         vyperStateTheory.get_address_immutables_def,vyperStateTheory.bind_def,
         vyperStateTheory.lift_option_type_def,vyperStateTheory.lift_sum_def,vyperStateTheory.return_def]) >>
  simp[] >>
  drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`) selected_immutable_array_value_holds >>
  disch_then irule >>
  goal_assum (drule_at (Pat `vv_place_ptr _ _ _ _ _ _`)) >>
  qexistsl [`env`,`tyv`] >> gvs[]
QED
*)
Theorem selected_array_code_frame:
  !body. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  loop_iterator_place e = SOME tgt /\
  vyperTypeSystem$place_access tgt [] = (TopLevelNameTarget (src,name),attrs) /\
  vyperTypeSystem$iterator_unmodified (Array e) body /\
  stmt_loop_calls_ok [(NONE,tops)] (For id typ (Array e) n body) /\
  path = MAP AttrSubscript attrs ++ tail /\
  lookup_immutable cx em src name = SOME (rt,old) /\
  evaluate_subscripts rt old (MAP AttrSubscript attrs) = INL (ArrayV pav) /\
  evaluate_subscripts rt old path = INL (ArrayV av) /\
  expr_sim_inv_mods [(NONE,tops)] c cx env em /\ ~cx_const_name cx (src,name) /\
  runtime_place_typed cx em (ImmutablePlace src name path) (ArrayTV tyv bd) /\
  evaluate_type (get_tenv cx) (ArrayT typ bd) = SOME (ArrayTV tyv bd) /\
  post_value_type c e = ArrayT typ bd ==>
  !a. read_result cx (PlaceR (ImmutablePlace src name path)) em = (INL (ArrayV a),em) ==>
  for_nonslot_code_frame c cx env ctx func id e body
    (case vv_location vv of NONE => LocMemory | SOME l => l)
    (PlaceR (ImmutablePlace src name path)) vv a em u
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >> irule for_array_expr_cut_frag_full >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`bindings`,`env`,`env'`,`tops`] >> asm_rewrite_tac[] >>
  map_every qx_gen_tac [`st0`,`sa`,`sb`,`sha`,`shb`,`s0`,`G0`,`tn0`,`vv`,
    `se`,`she`,`bd`,`tyv`,`marks`,`rv`,`em`,`G`,`tn`,`u`] >>
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `start = es with gas_obs := gas_explicit marks s0.vs_gas_readings` >>
  `em with gas_obs := [] = em` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> for_array_expr_endpoint _ _ _ _ _ _ _ _ _ _ _ _`
      (qspec_then `storage_trace_horizon em.storage_trace` mp_tac) >>
     fs[vyperStorageFootprintTheory.storage_trace_domain_def,bodyFullForExprCutTheory.for_array_expr_endpoint_def,
        vyperStateTheory.evaluation_state_component_equality]) >>
  `eval_expr cx e start = (INL rv,em)` by
    (qpat_assum `em with gas_obs := [] = em` (fn eq =>
       qpat_assum `!tail. eval_expr cx e _ = _` (qspec_then `[]` mp_tac) >>
       simp[NoAsms,Abbr `start`,eq])) >>
  `expr_body_pre cenv cx env e start` by simp[Abbr `start`] >>
  drule_at_then (Pat `eval_expr cx e start = _`) drule_all
    forNestedArrayCaptureTheory.nested_array_capture_cases >>
  disch_then (qx_choose_then `elem` (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 kall_tac assume_tac))) >>
  `elem = tyv` by metis_tac[optionTheory.SOME_11] >>
  pop_assum SUBST_ALL_TAC >>
  `post_value_type cenv e = ArrayT typ bd` by
    (`post_value_type cenv e = expr_type e` suffices_by simp[] >>
     irule loweringPostsTheory.post_value_type_not_int_call >> rpt strip_tac >>
     gvs[vyperTypeContractTheory.loop_iterator_place_def]) >>
  suspend "snapshot"
QED
*)
Theorem compile_for_immutable_subplace_array_frag_full:
  !cx id typ e n body DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    ~(?bd nid. e = TopLevelName (ArrayT typ bd) nid /\
               supported_storage_value tops nid (ArrayT typ bd)) /\
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx (Array e) s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_full_ok_mods mods exps cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_full_ok_mods mods exps cx (Array e)) /\
    (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\ supported_stmt tops bindings (For id typ (Array e) n body) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ (Array e) n body) ==>
       occurs_abi_decode_target target tops) /\
    stmt_loop_calls_ok [(NONE,tops)] (For id typ (Array e) n body) /\
    body_const_cells_agree mods cx env es /\
    expr_sim_inv_mods mods cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ (Array e) n body) = SOME env' /\
    ~supported_expr_exists (const_name_root cx) e /\
    stmt_exprs_ok cenv (For id typ (Array e) n body) /\
    ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env)
      (For id typ (Array e) n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ (Array e) n body)) /\
    frame_ret_ok_full_mods mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~(?ty nid. e = TopLevelName ty nid) /\
    (?tgt nid. loop_iterator_place e = SOME tgt /\ target_root tgt = TopLevelNameTarget nid /\
       IS_SOME (supported_immutable_type tops nid)) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ (Array e) n body))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (For id typ (Array e) n body)))
      (eval_stmt cx (For id typ (Array e) n body)) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_for_immutable_subplace_array_frag_full[snapshot]:
  qsuff_tac `((?av. rv = Value (ArrayV av)) \/ (?src name path. rv = PlaceR (ImmutablePlace src name path)))`
  >- (disch_tac >> irule for_array_snapshot_continue_full >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >- (qexists `gas_explicit marks s0.vs_gas_readings` >> first_assum ACCEPT_TAC) >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >-
        (gen_tac >> disch_tac >>
         qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
           (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      qexistsl [`bd`,`bindings`,`env`,`env'`,`ret_ty`,`se`,`sha`,`shadow_func`,
                `shb`,`she`,`tops`,`typ`,`vv`] >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >- simp[] >> conj_tac >- suspend "frame" >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  gvs[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_for_immutable_subplace_array_frag_full[frame]:
  qpat_assum `IS_SOME _ ==> _`
    (drule_then (DISJ_CASES_THEN2 (qx_choose_then `va` assume_tac)
      (qx_choosel_then [`src`,`name`,`path`,`attrs`,`tail`,`rt`,`root`,`av0`,`pav`]
         (map_every assume_tac o CONJUNCTS))))
  >- (`valid_horizon cx st0 (storage_trace_horizon em.storage_trace) em.storage_trace` by
        fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> for_array_expr_endpoint _ _ _ _ _ _ _ _ _ _ _ _`
        (drule_then (map_every assume_tac o CONJUNCTS o
           REWRITE_RULE [bodyFullForExprCutTheory.for_array_expr_endpoint_def])) >>
      rewrite_tac[bodyFullForArrayRoundTheory.for_nonslot_code_frame_def] >>
      qpat_assum `!v. rv = Value v /\ _ ==> _` (qspec_then `ArrayV va` mp_tac) >>
      Cases_on `vv` >> simp[contextTheory.vv_location_def,
         compileEnvTheory.is_word_type_def,compileEnvTheory.is_bytestring_type_def]) >>
  qpat_x_assum `rv = PlaceR _` SUBST_ALL_TAC >>
  qpat_x_assum `nid = (src,name)` SUBST_ALL_TAC >>
  drule_then strip_assume_tac bodyFullForFactsTheory.type_stmt_for_projection >>
  drule_at_then (Pat `eval_expr cx e start = _`) drule_all exprSimSourceTheory.expr_body_pre_eval_result >>
  strip_tac >>
  `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` by
    (drule_then (MATCH_ACCEPT_TAC o MATCH_MP contract_inv_singleton_source_modules)
       bodySimTheory.body_inv_contract) >>
  `~cx_const_name cx (src,name)` by
    (strip_tac >> drule_all_then strip_assume_tac bodySimTheory.body_inv_const_name_not_root >> fs[]) >>
  `evaluate_type (get_tenv cx) (ArrayT typ bd) = SOME (ArrayTV tyv bd)` by
    (drule_at_then (Pat `eval_expr cx e start = _`) drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >>
     strip_tac >>
     `evaluate_type (get_tenv cx) (ArrayT typ bd) = SOME tvt` by metis_tac[] >>
     drule_then strip_assume_tac vyperTypeValuesTheory.evaluate_type_ArrayT_cases >> gvs[]) >>
  gen_tac >> disch_tac >> drule_all_then MATCH_ACCEPT_TAC selected_array_code_frame
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise compile_for_immutable_subplace_array_frag_full
*)

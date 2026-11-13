Theory bodyForImmutableArrayPtr
Ancestors bodyPtrPreds bodyPtrDefs bodySimDeclCases
  stmtSimForArray exprSimHypsDefs exprSimHyps bodySim bodyExprPreFacts
  vyperAST vyperInterpreter vyperState vyperValue vyperTyping
  vyperTypeSystem vyperTypeInvariants vyperTypeValues
  supportedStmts supportedStmtTraverse allocLimits compileVyper
  vyperTypeCallGraph exprLoweringProps finite_map list vyperTypeCallStackSoundness
  whitelistForIterImmSource whitelistForIterImmFrame
  bodyStorageMetadata exprSimTopLevelProps valueEncodingProps valueEncodingTyping
  vyperTypeEnv arithmetic valueEncoding stmtSimProps stmtLoweringMono loweringPosts
  forPtrArraySemantic exprSimWordArgs vyperBareGlobalName
  whitelistForIterImmCopy exprSimCopy vyperValueOperation compileEnv
Libs monadsyntax

val _ = Parse.hide "body";

Theorem body_for_immutable_array_ptr:
  (!tenv s'' tyv t s3 vs t' s4 x t''.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) /\
     eval_iterator cx (Array (TopLevelName (ArrayT typ bd) (src,name))) s3 = (INL vs,t') /\
     check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s4 = (INL x,t'') ==>
     body_for_ptr_ok cx tyv id body vs) /\
  (!tenv s'' tyv t.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) ==>
     body_iterator_ptr_ok cx (Array (TopLevelName (ArrayT typ bd) (src,name)))) ==>
  body_stmt_ptr_ok cx (For id typ (Array (TopLevelName (ArrayT typ bd) (src,name))) n body)
Proof
  strip_tac >> rewrite_tac[body_stmt_ptr_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `well_typed_expr env (TopLevelName (ArrayT typ bd) (src,name)) /\
   id NOTIN FDOM env.var_types /\
   iterator_unmodified (Array (TopLevelName (ArrayT typ bd) (src,name))) body /\
   ?env_b. type_stmts (extend_local env id typ F) ret_ty body = SOME env_b` by
    gvs[type_stmt_def, well_typed_iterator_def, expr_type_def,
        optionTheory.IS_SOME_EXISTS, AllCaseEqs()] >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   IS_SOME (supported_immutable_type tops (src,name)) /\ bound_length bd <= n` by
    fs[body_inv_def, supported_stmt_def, supported_iterator_def] >>
  `?t. supported_immutable_type tops (src,name) = SOME t` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  drule_all supported_immutable_type_find_NONE >> strip_tac >> gvs[] >>
  `FLOOKUP env.bare_globals (NONE,name) = SOME (ArrayT typ bd)` by
    (irule toplevel_find_NONE_bare_global >> fs[expr_sim_inv_def] >> metis_tac[]) >>
  drule_all immutable_array_source_ready >> strip_tac >>
  drule evaluate_type_ArrayT_cases >> strip_tac >> gvs[] >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME tv` >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule declared_name_unbound >> metis_tac[]) >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     qpat_x_assum `!id entry. lookup_scopes _ _ = _ ==> _` drule >>
     simp[FLOOKUP_DEF]) >>
  qmatch_asmsub_abbrev_tac `INL (MAP Value vs)` >>
  `LENGTH vs <= bound_length bd /\ bound_length bd < dimword (:256) /\
   (case bd of Fixed cap => LENGTH vs = cap | Dynamic cap => T)` by
    suspend "bounds" >>
  `LENGTH vs <= n` by decide_tac >>
  `eval_iterator cx (Array (TopLevelName (ArrayT typ bd) (cenv.ce_module,name)))
      es = (INL (MAP Value vs),es)` by
    (`es with gas_obs := es.gas_obs = es` by
       simp[vyperStateTheory.evaluation_state_component_equality] >>
     qpat_x_assum `!gs. eval_iterator _ _ _ = (INL (MAP Value vs),_)`
       (qspec_then `es.gas_obs` mp_tac) >> asm_rewrite_tac[]) >>
  `body_for_ptr_ok cx tv id body (MAP Value vs)` by
    (qpat_x_assum `!s3 vs t' s4 t''. _` mp_tac >>
     simp[lift_option_type_def, return_def, check_def, assert_def, compatible_bound_def] >>
     disch_then irule >> simp[] >> qexistsl_tac [`es`, `es`] >> gvs[]) >>
  suspend "static"
QED

Resume body_for_immutable_array_ptr[static]:
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `supported_stmts tops bindings body /\
   ~supported_stmts_expr_exists expr_internal_call_root body` by
    fs[supported_stmt_def, supported_iterator_def] >>
  `type_memory_bytes cenv typ < 2 ** 64` by
    fs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
       alloc_limits_stmt_def, stmt_valued_return_def] >>
  `type_memory_bytes cenv typ = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `elem_size_in_location cenv LocCode typ = type_memory_size tv` by
    simp[elem_size_in_location_def, is_slot_addressed_def] >>
  `0 < type_memory_size tv` by metis_tac[immutable_array_element_size_positive] >>
  `type_memory_bytes cenv typ + 64 < dimword (:256)` by
    (fs[wordsTheory.dimword_def] >> decide_tac) >>
  `!k. k < LENGTH vs ==> value_has_type tv (EL k vs)` by suspend "typed" >>
  suspend "callbacks"
QED

Resume body_for_immutable_array_ptr[callbacks]:
  `stmts_exprs_ok (cenv with ce_var_type updated_by (id =+ SOME typ)) body` by
    fs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
       stmts_exprs_ok_thm, alloc_limits_stmt_def, stmt_valued_return_def] >>
  `call_evaluation_safe cx (int_calls_stmts body)` by
    (fs[int_calls_stmt_def] >> metis_tac[call_evaluation_safe_append_right]) >>
  qabbrev_tac `P = \ei. expr_sim_inv cenv cx env ei /\
    lookup_immutable cx ei cenv.ce_module name = lookup_immutable cx es cenv.ce_module name` >>
  `!ei s. P ei /\ stmt_state_rel ctx func cenv cx ei s ==>
    (case bd of Fixed cap => T | Dynamic cap =>
       ?av. immutable_holds cenv cx (ArrayT typ (Dynamic cap))
               (Value (ArrayV av)) (n2w off) ei s /\
            value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
            LENGTH vs = array_length (ArrayTV tv (Dynamic cap)) av) /\
    (!k. k < LENGTH vs ==> immutable_holds cenv cx typ (Value (EL k vs))
      (n2w off + n2w ((case bd of Fixed cap => 0 | Dynamic cap => 32) +
                      k * type_memory_size tv)) ei s)` by suspend "source" >>
  `!st0 bc sd ex inc ei k.
    declare_local cenv id typ st0 = (bc,sd) /\ P ei /\
    lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs ==>
    stmt_frag_ptr d ctx PG func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ret_ty body) (eval_stmts cx body)
      (ei with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes;
        gas_obs := []|>)` by suspend "body" >>
  `!ei k gs r es2. P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
    eval_stmts cx body (ei with <|scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes;
      gas_obs := gs|>) = (r,es2) ==>
    (!ex inc. stmt_res_ok (InLoop ex inc) r) /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)` by suspend "scope" >>
  `P (es with gas_obs := [])` by
    simp[Abbr `P`, expr_sim_inv_gas_obs, lookup_immutable_def] >>
  suspend "loop"
QED

Resume body_for_immutable_array_ptr[bounds]:
  `bound_length bd < dimword (:256)` by
    (qpat_x_assum `evaluate_type _ (ArrayT _ _) = _` mp_tac >>
     simp[evaluate_type_def, AllCaseEqs(), type_slot_size_def] >>
     rpt strip_tac >> Cases_on `bd` >> fs[type_slot_size_def, bound_length_def] >>
     `n' <= n' * type_slot_size tv` by
       (irule LESS_EQ_TRANS >> qexists_tac `n' * 1` >> simp[]) >> decide_tac) >>
  Cases_on `bd` >> Cases_on `av` >>
  gvs[value_has_type_def, array_elements_def, bound_length_def, Abbr `vs`]
QED

Resume body_for_immutable_array_ptr[typed]:
  gen_tac >> strip_tac >>
  Cases_on `bd` >> Cases_on `av` >>
  gvs[value_has_type_def, Abbr `vs`]
  >- (irule (cj 1 fixed_array_elements_typed) >> simp[value_has_type_def] >> metis_tac[]) >>
  gvs[array_elements_def, all_have_type_EVERY, EVERY_EL]
QED

Resume body_for_immutable_array_ptr[source]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `P ei` mp_tac >> simp[Abbr `P`] >> strip_tac >>
  `lookup_immutable cx ei cenv.ce_module name = SOME (ArrayTV tv bd,ArrayV av)` by
    gvs[lookup_immutable_def] >>
  `immutable_holds cenv cx (ArrayT typ bd) (Value (ArrayV av)) (n2w off) ei s` by
    (simp[immutable_holds_def, read_result_def, return_def] >>
     qexistsl_tac [`name`, `off`, `ArrayTV tv bd`, `ArrayV av`, `0`] >>
     simp[sub_layout_def] >>
     qpat_x_assum `lookup_immutable cx ei _ name = SOME _` mp_tac >>
     Cases_on `ALOOKUP ei.immutables cx.txn.target` >> simp[lookup_immutable_def]) >>
  conj_tac
  >- (Cases_on `bd` >> simp[] >> qexists_tac `av` >>
      Cases_on `av` >> gvs[value_has_type_def, array_elements_def, array_length_def, Abbr `vs`]) >>
  rpt strip_tac >> once_rewrite_tac[ADD_COMM] >>
  irule (cj 1 immutable_iter_element_ready) >> simp[] >>
  qexistsl_tac [`av`, `Value (ArrayV av)`] >>
  simp[read_result_def, return_def, Abbr `vs`] >>
  metis_tac[value_has_type_val_wf]
QED

Resume body_for_immutable_array_ptr[body]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `P ei` mp_tac >> simp[Abbr `P`] >> strip_tac >>
  `vs <> []` by (Cases_on `vs` >> fs[]) >>
  `body_stmts_ptr_ok cx body` by
    (fs[body_for_ptr_ok_def] >> Cases_on `vs` >> gvs[read_result_def, return_def]) >>
  `!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) body ==>
    occurs_abi_decode_target target tops` by fs[supported_stmt_expr_exists_def] >>
  `value_has_type tv (EL k vs)` by simp[] >>
  `expr_sim_inv cenv cx env (ei with gas_obs := [])` by simp[expr_sim_inv_gas_obs] >>
  `lookup_scopes id (ei with gas_obs := []).scopes = NONE` by simp[] >>
  drule_all for_array_body_fragment_ptr >>
  disch_then (qspecl_then [`inc`, `ex`] mp_tac) >> simp[]
QED

Resume body_for_immutable_array_ptr[scope]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `P ei` mp_tac >> simp[Abbr `P`] >> strip_tac >>
  `expr_sim_inv cenv cx env (ei with gas_obs := gs)` by simp[expr_sim_inv_gas_obs] >>
  `value_has_type tv (EL k vs)` by simp[] >>
  `lookup_scopes id (ei with gas_obs := gs).scopes = NONE` by simp[] >>
  `eval_stmts cx body
    ((ei with gas_obs := gs) with scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) ::
        (ei with gas_obs := gs).scopes) = (r,es2)` by simp[] >>
  conj_tac >- (drule_all array_body_result_ok >> simp[]) >>
  drule_all array_body_scope_shape >> strip_tac >>
  qexistsl_tac [`sc`, `rest`] >> simp[] >> strip_tac >>
  `expr_sim_inv cenv cx env (es2 with scopes := rest)` by
    (irule expr_sim_inv_for_pop >> metis_tac[]) >>
  `lookup_scopes id rest = NONE` by
    (Cases_on `lookup_scopes id rest` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     qpat_x_assum `!id entry. lookup_scopes _ _ = _ ==> _` drule >> simp[FLOOKUP_DEF]) >>
  simp[] >>
  `env_context_consistent (extend_local env id typ F) cx` by
    (fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def,
        extend_local_def] >> metis_tac[]) >>
  `FLOOKUP (extend_local env id typ F).bare_globals (NONE,name) =
     SOME (ArrayT typ bd)` by simp[extend_local_def] >>
  drule_all immutable_array_body_observation >>
  gvs[lookup_immutable_def, extend_local_def]
QED

Resume body_for_immutable_array_ptr[loop]:
  FAIL_TAC "immutable pointer loop bridge"
QED

Finalise body_for_immutable_array_ptr

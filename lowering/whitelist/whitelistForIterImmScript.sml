(* Immutable array iteration uses the location-aware element copy.
   Calldata-origin array arguments are decoded to memory before the body;
   they belong to the memory-valued iterable case, not this leaf. *)
Theory whitelistForIterImm
Ancestors
  whitelistForIterImmCopy whitelistForIterImmSource whitelistForIterImmFrame
  whitelistForIterImmLoop
  bodySimDeclCases whitelistForIterDynFrag whitelistForIterDynLoop
  exprSimSource bodyExprPreFacts stmtSimProps exprSimHypsDefs list finite_map
  bodySim bodySimStmtCases allocLimits exprSimHyps exprLoweringProps
  stmtSimDecl stmtSimFor stmtSimForParts stmtLowering stmtLoweringMono
  stmtSimForArray stmtSimForArrayFrag stmtSimForArrayLoop
  vyperTyping fragExec compileEnv supportedStmts supportedStmtTraverse
  compileVyper vyperTypeCallGraph vyperTypeCallStackSoundness vyperAST
  vyperInterpreter vyperState vyperValue vyperValueOperation vyperTypeSystem
  vyperTypeInvariants vyperTypeValues vyperTypeEnv valueEncoding
  valueEncodingProps valueEncodingTyping exprSimAggregateEncoding
  exprSimTopLevelImmutable exprSimCopy loweringPosts venomState arithmetic
Libs
  monadsyntax

(* Typing and semantic entry facts, independent of the generated loop blocks. *)
Theorem immutable_for_typing_ready[local]:
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
  FLOOKUP env.bare_globals (src,name) = SOME (ArrayT typ bd) /\
  type_stmt env ret_ty
    (For id typ (Array (TopLevelName (ArrayT typ bd) (src,name))) n stmts) =
    SOME env' ==>
  ?off ts imms tv av env_b.
    env' = env /\ id NOTIN FDOM env.var_types /\
    iterator_unmodified (Array (TopLevelName (ArrayT typ bd) (src,name))) stmts /\
    type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
    src = cenv.ce_module /\
    FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name name ts = NONE /\
    ALOOKUP es.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables src imms) name = SOME (ArrayTV tv bd,ArrayV av) /\
    evaluate_type (get_tenv cx) typ = SOME tv /\
    evaluate_type (get_tenv cx) (ArrayT typ bd) = SOME (ArrayTV tv bd) /\
    value_has_type (ArrayTV tv bd) (ArrayV av) /\
    well_formed_type_value (ArrayTV tv bd) /\
    off + type_memory_size (ArrayTV tv bd) < dimword (:256) /\
    (!gs. eval_iterator cx (Array (TopLevelName (ArrayT typ bd) (src,name)))
      (es with gas_obs := gs) =
      (INL (array_elements (ArrayTV tv bd) av), es with gas_obs := gs)) /\
    FLOOKUP cenv.ce_vars id = NONE /\ lookup_scopes id es.scopes = NONE
Proof
  strip_tac >>
  `env' = env /\ id NOTIN FDOM env.var_types /\
   iterator_unmodified (Array (TopLevelName (ArrayT typ bd) (src,name))) stmts /\
   ?env_b. type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b` by
    gvs[type_stmt_def, well_typed_iterator_def, expr_type_def,
        optionTheory.IS_SOME_EXISTS, AllCaseEqs()] >>
  drule_all immutable_array_source_ready >> strip_tac >>
  drule evaluate_type_ArrayT_cases >> strip_tac >> gvs[] >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule declared_name_unbound >> metis_tac[]) >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     qpat_x_assum `!id entry. lookup_scopes _ _ = _ ==> _` drule >>
     simp[FLOOKUP_DEF]) >>
  metis_tac[]
QED

Theorem immutable_for_elements_ready[local]:
  evaluate_type tenv (ArrayT typ bd) = SOME (ArrayTV tv bd) /\
  value_has_type (ArrayTV tv bd) (ArrayV av) ==>
  LENGTH (array_elements (ArrayTV tv bd) av) <= bound_length bd /\
  bound_length bd < dimword (:256) /\
  ((case bd of Fixed _ => T | Dynamic _ => F) ==>
    LENGTH (array_elements (ArrayTV tv bd) av) = bound_length bd)
Proof
  strip_tac >>
  `bound_length bd < dimword (:256)` by
    (qpat_x_assum `evaluate_type _ _ = _` mp_tac >>
     simp[evaluate_type_def, AllCaseEqs(), type_slot_size_def] >>
     rpt strip_tac >>
     Cases_on `bd` >> fs[type_slot_size_def, bound_length_def] >>
     `n <= n * type_slot_size tv` by
       (irule LESS_EQ_TRANS >> qexists_tac `n * 1` >> simp[]) >>
     decide_tac) >>
  Cases_on `bd` >> Cases_on `av` >>
  gvs[value_has_type_def, array_elements_def, bound_length_def]
QED

(* The immutable snapshot is preserved alongside the ordinary loop environment. *)
Theorem immutable_for_scope_callback[local]:
  expr_sim_inv cenv cx env ei /\ id NOTIN FDOM env.var_types /\
  evaluate_type (get_tenv cx) typ = SOME tv /\ value_has_type tv v /\
  type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
  call_evaluation_safe cx (int_calls_stmts stmts) /\
  supported_program tops /\ get_module_code cx NONE = SOME tops /\
  supported_stmts tops bindings stmts /\
  FLOOKUP env.bare_globals (src,name) = SOME (ArrayT typ bd) /\
  iterator_unmodified (Array (TopLevelName (ArrayT typ bd) (src,name))) stmts /\
  ~supported_stmts_expr_exists expr_internal_call_root stmts /\
  lookup_scopes id ei.scopes = NONE /\
  eval_stmts cx stmts
    (ei with scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := v; popped := []|>)) :: ei.scopes) = (r,ef) ==>
  (!ex inc. stmt_res_ok (InLoop ex inc) r) /\
  ?sc rest. ef.scopes = sc::rest /\
    (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
    ((r = INL () \/ r = INR ContinueException) ==>
      expr_sim_inv cenv cx env (ef with scopes := rest) /\
      lookup_immutable cx (ef with scopes := rest) src name = lookup_immutable cx ei src name /\
      lookup_scopes id rest = NONE)
Proof
  strip_tac >>
  `!ex inc. stmt_res_ok (InLoop ex inc) r` by
    (drule_all array_body_result_ok >> simp[]) >>
  drule_all array_body_scope_shape >> strip_tac >>
  simp[] >> strip_tac >>
  `expr_sim_inv cenv cx env (ef with scopes := rest)` by
    (irule expr_sim_inv_for_pop >> metis_tac[]) >>
  `lookup_scopes id rest = NONE` by
    (Cases_on `lookup_scopes id rest` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     qpat_x_assum `!id entry. lookup_scopes _ _ = _ ==> _` drule >>
     simp[FLOOKUP_DEF]) >>
  simp[] >>
  `env_context_consistent (extend_local env id typ F) cx` by
    (fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def,
        extend_local_def] >> metis_tac[]) >>
  `FLOOKUP (extend_local env id typ F).bare_globals (src,name) =
     SOME (ArrayT typ bd)` by simp[extend_local_def] >>
  drule_all immutable_array_body_observation >>
  simp[vyperBareGlobalNameTheory.lookup_immutable_def, extend_local_def]
QED

Theorem immutable_for_source_callback[local]:
  expr_sim_inv cenv cx env ei /\
  FLOOKUP env.bare_globals (src,name) = SOME (ArrayT typ bd) /\
  FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  lookup_immutable cx ei src name = SOME (ArrayTV tv bd,ArrayV av) /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  vs = array_elements (ArrayTV tv bd) av ==>
  (case bd of Fixed cap => T | Dynamic cap =>
    ?av. immutable_holds cenv cx (ArrayT typ (Dynamic cap))
           (Value (ArrayV av)) (n2w off) ei s /\
         value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
         LENGTH vs = array_length (ArrayTV tv (Dynamic cap)) av) /\
  (!k. k < LENGTH vs ==> immutable_holds cenv cx typ (Value (EL k vs))
    (n2w off + n2w ((case bd of Fixed cap => 0 | Dynamic cap => 32) +
                    k * type_memory_size tv)) ei s)
Proof
  strip_tac >> drule_all immutable_array_source_ready >> strip_tac >>
  gvs[vyperBareGlobalNameTheory.lookup_immutable_def] >>
  `immutable_holds cenv cx (ArrayT typ bd) (Value (ArrayV av)) (n2w off) ei s` by
    (simp[immutable_holds_def, read_result_def, return_def] >>
     qexistsl_tac [`name`, `off`, `ArrayTV tv bd`, `ArrayV av`, `0`] >>
     simp[sub_layout_def]) >>
  conj_tac
  >- (Cases_on `bd` >> simp[] >> qexists_tac `av` >>
      Cases_on `av` >> gvs[value_has_type_def, array_elements_def, array_length_def]) >>
  rpt strip_tac >> once_rewrite_tac[ADD_COMM] >>
  irule (cj 1 immutable_iter_element_ready) >> simp[] >>
  qexistsl_tac [`av`, `Value (ArrayV av)`] >>
  simp[read_result_def, return_def] >>
  metis_tac[value_has_type_val_wf]
QED

Theorem immutable_for_body_callback[local]:
  body_for_ok cx tv id stmts vs /\ body_inv tops ctx cenv cx /\
  supported_stmts tops bindings stmts /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (For id typ (Array (TopLevelName (ArrayT typ bd) (src,name))) n stmts) ==>
    occurs_abi_decode_target target tops) /\
  ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
  id NOTIN FDOM env.var_types /\ evaluate_type (get_tenv cx) typ = SOME tv /\
  (!k. k < LENGTH vs ==> value_has_type tv (EL k vs)) /\
  type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
  stmt_exprs_ok cenv
    (For id typ (Array (TopLevelName (ArrayT typ bd) (src,name))) n stmts) /\
  type_memory_bytes cenv typ < 2 ** 64 /\
  call_evaluation_safe cx (int_calls_stmt
    (For id typ (Array (TopLevelName (ArrayT typ bd) (src,name))) n stmts)) /\
  frame_ret_ok ctx func cx RetQ cenv ret_ty ==>
  !st0 bc sd ex inc ei k.
    declare_local cenv id typ st0 = (bc,sd) /\
    (expr_sim_inv cenv cx env ei /\
     lookup_immutable cx ei src name = lookup_immutable cx es src name) /\
    lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs ==>
    stmt_frag ctx func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ret_ty stmts) (eval_stmts cx stmts)
      (ei with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `vs <> []` by (Cases_on `vs` >> fs[]) >>
  `body_stmts_ok cx stmts` by fs[body_for_ok_def] >>
  `!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) stmts ==>
    occurs_abi_decode_target target tops` by fs[supported_stmt_expr_exists_def] >>
  `EVERY (stmt_exprs_ok cenv) stmts` by
    fs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
       stmts_exprs_ok_EVERY, alloc_limits_stmt_def, stmt_valued_return_def] >>
  `call_evaluation_safe cx (int_calls_stmts stmts)` by
    (fs[int_calls_stmt_def] >> metis_tac[call_evaluation_safe_append_right]) >>
  irule array_body_fragment_callback >> metis_tac[]
QED

Theorem body_for_immutable_array:
  !cx id typ bd src name n stmts tops bindings ctx func cenv env env'
   ret_ty lctx RetQ es.
    (!tenv s0 tyv t s1 vs t1 s2 x t2.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s0 =
         (INL tyv,t) /\
       eval_iterator cx (Array (TopLevelName (ArrayT typ bd) (src,name))) s1 =
         (INL vs,t1) /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s2 =
         (INL x,t2) ==>
       body_for_ok cx tyv id stmts vs) /\
    (!tenv s0 tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s0 =
         (INL tyv,t) ==>
       body_iterator_ok cx
         (Array (TopLevelName (ArrayT typ bd) (src,name)))) /\
    body_inv tops ctx cenv cx /\
    supported_type_namespace typ /\ supported_stmts tops bindings stmts /\
    ~supported_stmts_expr_exists expr_internal_call_root stmts /\
    bound_length bd <= n /\
    FLOOKUP env.bare_globals (src,name) = SOME (ArrayT typ bd) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target)
       (For id typ (Array (TopLevelName (ArrayT typ bd) (src,name))) n stmts)
       ==> occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty
      (For id typ (Array (TopLevelName (ArrayT typ bd) (src,name))) n stmts) =
      SOME env' /\
    stmt_exprs_ok cenv
      (For id typ (Array (TopLevelName (ArrayT typ bd) (src,name))) n stmts) /\
    call_evaluation_safe cx
      (int_calls_stmt
        (For id typ (Array (TopLevelName (ArrayT typ bd) (src,name))) n stmts)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
        (For id typ (Array (TopLevelName (ArrayT typ bd) (src,name))) n stmts))
      (eval_stmt cx
        (For id typ (Array (TopLevelName (ArrayT typ bd) (src,name))) n stmts)) es
Proof
  rpt gen_tac >> strip_tac >>
  drule_all immutable_for_typing_ready >> strip_tac >> gvs[] >>
  drule_all immutable_for_elements_ready >> strip_tac >>
  qmatch_asmsub_abbrev_tac `LENGTH vs <= bound_length bd` >>
  `LENGTH vs <= n` by decide_tac >>
  `eval_iterator cx (Array (TopLevelName (ArrayT typ bd) (cenv.ce_module,name)))
      es = (INL vs,es)` by
    (`es = es with gas_obs := es.gas_obs` by
       simp[vyperStateTheory.evaluation_state_component_equality] >>
     pop_assum SUBST1_TAC >>
     qpat_assum `!gs. eval_iterator _ _ _ = _` (fn th => rewrite_tac [th])) >>
  `body_for_ok cx tv id stmts vs` by
    (qpat_x_assum `!s1 vs t1 s2 t2. _` mp_tac >>
     simp[return_def, check_def, assert_def, compatible_bound_def] >>
     disch_then irule >> simp[] >> qexistsl_tac [`es`, `es`] >> simp[]) >>
  cheat
QED

(* Shared statement facts used by the body simulations. *)

Theory bodySimStmtFacts
Ancestors
  bodyStorageMetadata targetPlaceSim exprSimSource bodyExprPreFacts
  exprSimTopLevelProps exprSimHypsDefs vyperStorageLayoutSafety list
  finite_map bodySim allocLimits allocLimitsProps
  exprSimHyps stmtLowering compileEnv supportedExprTraverse
  supportedStmtTraverse supportedStmts vyperAST vyperState
  vyperTypeSystem vyperTypeCallGraph vyperTypeCallStackSoundness supportedExprs
  stmtSimDeclStore vyperTypeEvalSoundness vyperTypeInvariants exprReasonOperand
  compileVyper supportedTypes stmtSimAssignAttr memoryLocalRhsProps
  exprOpenMain gasContext exprLowering vyperCompiler
  option tupleTargetStoreProps vyperTypeEnv accountsRelProps
  exprSimUnwrap exprSimFieldLayout exprSimAttributeFields vyperPlaceResultTyping
Libs
  monadsyntax

Definition reason_covered_def:
  reason_covered cenv r <=>
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_vv_ok vv) \/
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_storage_vv vv)
End

Theorem well_typed_literal_string[local]:
  !ty s. well_typed_literal ty (StringL s) ==> ?n. ty = BaseT (StringT n)
Proof
  Cases >> simp[well_typed_literal_def] >>
  rename1 `BaseT b` >> Cases_on `b` >> simp[well_typed_literal_def]
QED

Theorem concat_buffer_type_not_word[local]:
  ~is_word_type (concat_buffer_type ty n)
Proof
  simp[exprLoweringTheory.concat_buffer_type_def] >>
  Cases_on `ty` >> simp[is_word_type_def] >>
  Cases_on `b` >> simp[is_word_type_def]
QED

Theorem lowered_value_type_not_call_word[local]:
  !cenv e. (!a t es d. e <> Call a t es d) /\ ~is_word_type (expr_type e) ==>
           ~is_word_type (lowered_value_type cenv e)
Proof
  ho_match_mp_tac exprLoweringTheory.lowered_value_type_ind >>
  rw[exprLoweringTheory.lowered_value_type_def, is_word_type_def, expr_type_def,
     concat_buffer_type_not_word]
QED

(* TEMPORARILY CHEATED - SCRATCH SEQ-8501 census (never lands)
Proof
  rpt gen_tac >> strip_tac >>
  `?n. expr_type e = BaseT (StringT n)` by
    (Cases_on `?t str. e = Literal t (StringL str)`
     >- (gvs[well_typed_expr_def, expr_type_def] >>
         metis_tac[well_typed_literal_string]) >>
     `case expr_type e of BaseT (StringT _) => T | _ => F` by
       (Cases_on `e` >> fs[supported_string_reason_def] >>
        rename1 `Literal _ lit` >> Cases_on `lit` >>
        fs[supported_string_reason_def]) >>
     Cases_on `expr_type e` >> fs[] >>
     rename1 `BaseT b` >> Cases_on `b` >> fs[]) >>
  `~is_word_type (lowered_value_type cenv e)` by
    (irule lowered_value_type_not_call_word >>
     gvs[is_word_type_def] >> rpt strip_tac >>
     gvs[supported_string_reason_def, supported_pure_expr_def]) >>
  qspecl_then [`cenv`, `env`, `e`, `n`] mp_tac compile_expr_string_reason >>
  impl_tac >- (fs[expr_sim_inv_def] >> metis_tac[]) >>
  fs[reason_covered_def] >> metis_tac[]
QED
*)
Theorem supported_reason_code:
  !cenv cx env es tops e.
    expr_sim_inv cenv cx env es /\
    supported_string_reason tops e /\ well_typed_expr env e /\
    ~reason_covered cenv e ==>
    !sa vv sb. compile_expr cenv (expr_type e) e sa = (vv, sb) ==>
               reason_code_vv vv
Proof
  cheat
QED

Theorem expr_body_pre_eval_result:
  !cenv cx env e es res es'.
    expr_body_pre cenv cx env e es /\ eval_expr cx e es = (res, es') ==>
    expr_sim_inv cenv cx env es'
Proof
  metis_tac[exprSimSourceTheory.expr_body_pre_eval_result]
QED

Theorem expr_body_pre_eval:
  !cenv cx env e es res es'.
    expr_body_pre cenv cx env e es /\
    (do result <- eval_expr cx e; read_result cx result od) es = (res, es') ==>
    expr_sim_inv cenv cx env es' /\
    !v. res = INL v ==> value_runtime_typed env (expr_type e) v
Proof
  rpt strip_tac >>
  `state_well_typed es' /\
   (case res of INL v => value_runtime_typed env (expr_type e) v | INR _ => T)` by
    (drule_at (Pat `bind _ _ _ = _`) eval_expr_read_type_sound >>
     disch_then (qspec_then `env` mp_tac) >>
     gvs[expr_body_pre_def, expr_sim_inv_def]) >>
  gvs[] >>
  qpat_x_assum `(do result <- eval_expr _ _; read_result _ result od) _ = _` mp_tac >>
  simp[NoAsms, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[] >>
  drule_all expr_body_pre_eval_result >> simp[]
QED

Theorem body_inv_storage_var_types:
  !tops ctx cenv cx.
    body_inv tops ctx cenv cx /\
    (!src ts. get_module_code cx src = SOME ts ==> src = NONE) ==>
    !src id ts tr typ id_str.
      get_module_code cx src = SOME ts /\
      find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) ==>
      cenv.ce_hashmap_info (src,id) = NONE /\
      cenv.ce_module_var_type (src,id) = SOME typ
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `src = NONE` by metis_tac[] >> gvs[body_inv_def] >>
  drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  drule_all build_maps_variable >> simp[]
QED

Theorem env_assignable_find_NONE:
  !env cx st src id ty.
    env_consistent env cx st /\
    FLOOKUP env.bare_global_assignable (src, id) = SOME ty ==>
    ?ts. get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE
Proof
  rw[env_consistent_def, env_context_consistent_def] >>
  first_x_assum drule >> strip_tac >> simp[]
QED

(* TEMPORARILY CHEATED - SCRATCH SEQ-8501 census (never lands)
Proof
  rpt gen_tac >> strip_tac >>
  drule topcopy_not_bytestring >>
  Cases_on `t` >> simp[has_length_word_def, is_bytestring_type_def] >>
  Cases_on `b` >> gvs[has_length_word_def, is_bytestring_type_def]
QED
*)
Theorem topcopy_no_length_word:
  !tops t. supported_storage_type tops t /\
    (!elem n. t <> ArrayT elem (Dynamic n)) ==> ~has_length_word t
Proof
  cheat
QED

Theorem body_inv_mcopy:
  !tops ctx cenv cx. body_inv tops ctx cenv cx ==> cenv.ce_target CapMcopy
Proof
  rw[body_inv_def] >> Cases_on `cx.in_deploy` >> gvs[]
  >- (gvs[lower_vyper_deploy_unit_def, AllCaseEqs()] >>
      rpt (pairarg_tac >> gvs[]) >>
      gvs[vyperCompilerTheory.run_deploy_lowering_def, AllCaseEqs(),
          vyperCompilerTheory.lowering_policy_ok_def]) >>
  gvs[lower_vyper_runtime_unit_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[vyperCompilerTheory.run_lowering_def,
      vyperCompilerTheory.run_grouped_lowering_def, AllCaseEqs(),
      vyperCompilerTheory.lowering_policy_ok_def]
QED

Theorem tuple_target_local_ptr:
  !cenv cx env es id ty tv.
    expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
    FLOOKUP env.var_types id = SOME ty /\ 0 < type_memory_bytes cenv ty /\
    evaluate_type (get_tenv cx) ty = SOME tv ==>
    ?p sz vt.
      FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
      cenv.ce_var_type id = SOME vt /\
      if is_word_type ty then is_word_type vt
      else
        (vt = ty \/ is_bytestring_type vt /\ is_bytestring_type ty) /\
        type_memory_bytes cenv ty = type_memory_size tv /\
        ?vtv. evaluate_type (get_tenv cx) vt = SOME vtv /\
              type_memory_bytes cenv vt = type_memory_size vtv /\
              0 < type_memory_size vtv /\
              type_memory_size vtv + 64 < dimword (:256)
Proof
  rpt strip_tac >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    metis_tac[expr_sim_inv_local] >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  qexistsl_tac [`p`, `sz`, `ty`] >> simp[] >>
  Cases_on `is_word_type ty` >> simp[] >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `type_memory_bytes cenv ty < 2 ** 64` by metis_tac[locals_alloc_ok_def] >>
  metis_tac[allocation_limit_word_room]
QED

Theorem tuple_target_local_lays_out:
  !cenv cx env es1 id ty tv v entry.
    expr_sim_inv cenv cx env es1 /\ FLOOKUP env.var_types id = SOME ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    lookup_scopes id es1.scopes = SOME entry ==>
    if is_word_type ty then store_lays_out tv entry.type v
    else
      ?vt. cenv.ce_var_type id = SOME vt /\
           evaluate_type (get_tenv cx) vt = SOME entry.type /\
           value_has_type entry.type v
Proof
  rpt strip_tac >>
  `evaluate_type (get_tenv cx) ty = SOME entry.type` by
    metis_tac[expr_sim_inv_local] >>
  `entry.type = tv` by metis_tac[optionTheory.SOME_11] >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  IF_CASES_TAC >> simp[] >> metis_tac[store_lays_out_typed]
QED

Theorem tuple_staging_bound:
  !cenv cx env es g e tys tvs.
    expr_sim_inv cenv cx env es /\
    stmt_exprs_ok cenv (Assign (TupleTarget g) e) /\
    expr_type e = TupleT tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    is_memory_view e ==>
    type_memory_size (TupleTV tvs) < dimword (:256)
Proof
  rpt strip_tac >>
  `type_memory_bytes cenv (TupleT tys) < 2 ** 64` by
    gvs[stmt_exprs_ok_flat, allocLimitsTheory.alloc_limits_stmt_def] >>
  `type_memory_bytes cenv (TupleT tys) = type_memory_size (TupleTV tvs)` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `type_memory_size (TupleTV tvs) + 64 < dimword (:256)` by
    metis_tac[allocation_limit_word_room] >>
  decide_tac
QED

Theorem body_tuple_target_local_aligned:
  expr_sim_inv cenv cx env es /\ FLOOKUP env.var_types id = SOME ty /\
  0 < type_memory_bytes cenv ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  tuple_target_aligned cenv cx (BaseTarget (NameTarget id)) ty tv
Proof
  rpt strip_tac >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  simp[tupleTargetStorePropsTheory.tuple_target_aligned_local] >>
  metis_tac[expr_sim_inv_local]
QED

Theorem body_tuple_target_local_layout:
  expr_sim_inv cenv cx env es /\
  well_typed_atarget env (BaseTarget (NameTarget id)) ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v ==>
  tuple_target_layout es.scopes (BaseTarget (NameTarget id)) ty tv v
Proof
  rpt strip_tac >>
  gvs[well_typed_atarget_def, well_typed_target_def,
      vyperTypeEnvTheory.type_place_target_NameTarget] >>
  `?entry. lookup_scopes id es.scopes = SOME entry /\ entry.assignable` by
    (fs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     metis_tac[]) >>
  `entry.type = tv` by metis_tac[expr_sim_inv_local, optionTheory.SOME_11] >>
  simp[tupleTargetStorePropsTheory.tuple_target_layout_local] >>
  metis_tac[store_lays_out_typed]
QED

Theorem body_tuple_target_local_room:
  expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
  FLOOKUP env.var_types id = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  type_memory_size tv + 64 < dimword (:256)
Proof
  rpt strip_tac >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `type_memory_bytes cenv ty < 2 ** 64` by metis_tac[locals_alloc_ok_def] >>
  metis_tac[allocation_limit_word_room]
QED

(* TEMPORARILY CHEATED - SCRATCH SEQ-8501 census (never lands)
Proof
  Cases_on `nsid` >> rename1 `(src, id)` >> rpt strip_tac >>
  drule supported_scalar_target_decl >> strip_tac >> gvs[] >>
  rename1 `is_word_type declared_ty` >>
  `get_module_code cx NONE = SOME tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE, id) = build_var_type_map tops (NONE, id)` by
    fs[body_inv_def] >>
  drule_all build_maps_variable >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  gvs[vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (drule_all env_assignable_find_NONE >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  `declared_ty = ty` by metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[] >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  drule_all exprSimTopLevelPropsTheory.toplevel_storage_ce_vars >> strip_tac >>
  simp[tupleTargetStorePropsTheory.tuple_target_aligned_toplevel] >>
  rpt strip_tac >> irule accountsRelPropsTheory.storage_dead_update_word_region >>
  qexistsl_tac [`NONE`, `id`, `[]`, `tv`] >>
  simp[vyperStorageLayoutSafetyTheory.declared_storage_region_def] >>
  metis_tac[exprSimUnwrapTheory.word_type_slot_size]
QED
*)
Theorem body_tuple_target_toplevel_aligned:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  supported_scalar_target tops nsid /\
  type_place_target env (TopLevelNameTarget nsid) = SOME (Type ty) /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  tuple_target_aligned cenv cx (BaseTarget (TopLevelNameTarget nsid)) ty tv
Proof
  cheat
QED

Theorem body_tuple_target_field_aligned:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  supported_storage_field_write tops nsid fld /\
  type_place_target env (AttributeTarget (TopLevelNameTarget nsid) fld) =
    SOME (Type ty) /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  tuple_target_aligned cenv cx
    (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) ty tv
Proof
  Cases_on `nsid` >> rename1 `(src, id)` >> rpt strip_tac >>
  drule supported_storage_field_write_decl >> strip_tac >> gvs[] >>
  `get_module_code cx NONE = SOME tops /\ supported_program tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE, id) =
     build_var_type_map tops (NONE, id)` by fs[body_inv_def] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  gvs[vyperTypeEnvTheory.type_place_target_AttributeTarget,
      vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (drule_all env_assignable_find_NONE >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  rename1 `attribute_type _ tgt_ty fld = SOME _` >>
  `tgt_ty = StructT sid` by
    metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[] >> drule_all build_maps_variable >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  gvs[] >>
  drule_all attribute_type_struct_field >> strip_tac >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `IS_SOME (evaluate_type _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  drule_all exprSimTopLevelPropsTheory.toplevel_storage_ce_vars >> strip_tac >>
  drule_all exprSimFieldLayoutTheory.struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all exprSimAttributeFieldsTheory.struct_field_type >> strip_tac >> gvs[] >>
  drule vyperPlaceResultTypingTheory.struct_field_slot_exists >> strip_tac >>
  drule_all exprSimFieldLayoutTheory.struct_field_offset_slots_eq >> strip_tac >>
  simp[tupleTargetStorePropsTheory.tuple_target_aligned_field] >>
  rpt gen_tac >> irule accountsRelPropsTheory.storage_dead_update_struct_word_field >>
  goal_assum (drule_at Any) >> qexistsl_tac [`NONE`, `id`] >>
  simp[vyperStorageLayoutSafetyTheory.declared_storage_region_def] >>
  metis_tac[exprSimUnwrapTheory.word_type_slot_size]
QED

Theorem body_tuple_target_ready:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  locals_alloc_ok cenv env /\ well_typed_atarget env g ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  ((?id lty. g = BaseTarget (NameTarget id) /\
            FLOOKUP env.var_types id = SOME lty /\
            0 < type_memory_bytes cenv lty) \/
   (?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
           supported_scalar_target tops nsid) \/
   (?nsid fld fty.
      g = BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld) /\
      supported_storage_field_write tops nsid fld /\
      type_place_target env (AttributeTarget (TopLevelNameTarget nsid) fld) =
        SOME (Type fty) /\ is_word_type fty)) ==>
  tuple_target_aligned cenv cx g ty tv /\
  (~is_word_type ty ==> type_memory_size tv + 64 < dimword (:256)) /\
  (!es1 v. expr_sim_inv cenv cx env es1 /\ value_has_type tv v ==>
     tuple_target_layout es1.scopes g ty tv v)
Proof
  rpt strip_tac >> gvs[tupleTargetStorePropsTheory.tuple_target_base_type]
  >- (gvs[vyperTypeEnvTheory.type_place_target_NameTarget] >>
      irule body_tuple_target_local_aligned >> metis_tac[])
  >- (gvs[vyperTypeEnvTheory.type_place_target_NameTarget] >>
      metis_tac[body_tuple_target_local_room])
  >- (irule body_tuple_target_local_layout >>
      simp[well_typed_atarget_def, well_typed_target_def] >> metis_tac[])
  >- (irule body_tuple_target_toplevel_aligned >> metis_tac[])
  >- (drule_all body_tuple_target_toplevel_aligned >>
      Cases_on `nsid` >>
      simp[tupleTargetStorePropsTheory.tuple_target_aligned_toplevel])
  >- simp[tupleTargetStorePropsTheory.tuple_target_layout_def]
  >- (irule body_tuple_target_field_aligned >> metis_tac[])
  >> simp[tupleTargetStorePropsTheory.tuple_target_layout_def]
QED

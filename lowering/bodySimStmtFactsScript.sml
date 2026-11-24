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
  compileVyper supportedTypes supportedDecls stmtSimAssignAttr memoryLocalRhsProps
  exprOpenMain gasContext exprLowering vyperCompiler
  bodyTypedTargetScope bodyInvCodeProps exprBodyPreProps linkedStorageMetadataProps alist
  bodyLoweringTargetProps vyperEvalOutcomeSuffix vyperTypeExprResult
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

Theorem expr_body_pre_eval_result:
  !cenv cx env e es res es'.
    expr_body_pre cenv cx env e es /\ eval_expr cx e es = (res, es') ==>
    expr_sim_inv cenv cx env es'
Proof
  metis_tac[exprSimSourceTheory.expr_body_pre_eval_result]
QED

Theorem expr_sim_inv_mods_eval_result[local]:
  expr_sim_inv_mods mods cenv cx env es /\ well_typed_expr env e /\
  call_evaluation_safe cx (int_calls_expr e) /\
  eval_expr cx e es = (res,es') ==>
  expr_sim_inv_mods mods cenv cx env es'
Proof
  strip_tac >>
  `IS_SOME es'.outcomes` by
    (irule eval_expr_outcomes_some >>
     gvs[expr_sim_inv_mods_def] >> metis_tac[]) >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ _` mp_tac >>
  simp[expr_sim_inv_mods_def] >> strip_tac >>
  drule_all_then assume_tac eval_expr_popped_keys_indexed >>
  qspecl_then [`cx`, `e`] (mp_tac o CONJUNCT1)
    (cj 5 eval_scc_type_sound_mutual) >>
  disch_then (qspecl_then [`env`, `es`, `res`, `es'`] mp_tac) >>
  impl_tac >- gvs[] >> strip_tac >>
  `outcomes_accounts_typed es'.outcomes` by
    (rw[outcomes_accounts_typed_def] >>
     drule (cj 5 eval_outcome_suffix_mutual) >> strip_tac >>
     drule_then irule outcome_suffix_EVERY >> gvs[outcomes_accounts_typed_def]) >>
  Cases_on `res` >> gvs[] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem expr_body_pre_eval_mods:
  expr_body_pre_mods mods cenv cx env e es /\
  (do result <- eval_expr cx e; read_result cx result od) es = (res,es') ==>
  expr_sim_inv_mods mods cenv cx env es' /\
  !v. res = INL v ==> value_runtime_typed env (expr_type e) v
Proof
  strip_tac >>
  fs[expr_body_pre_mods_def] >>
  `case res of INL v => value_runtime_typed env (expr_type e) v | INR _ => T` by
    (drule_at (Pat `bind _ _ _ = _`) eval_expr_read_type_sound >>
     disch_then (qspec_then `env` mp_tac) >>
     gvs[expr_sim_inv_mods_def]) >>
  qpat_x_assum `(do result <- eval_expr _ _; read_result _ result od) _ = _` mp_tac >>
  simp[NoAsms, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[] >>
  drule_all_then assume_tac expr_sim_inv_mods_eval_result >>
  rpt strip_tac >> gvs[]
QED

Theorem expr_body_pre_eval:
  !cenv cx env e es res es'.
    expr_body_pre cenv cx env e es /\
    (do result <- eval_expr cx e; read_result cx result od) es = (res, es') ==>
    expr_sim_inv cenv cx env es' /\
    !v. res = INL v ==> value_runtime_typed env (expr_type e) v
Proof
  simp[expr_body_pre_split_def, expr_sim_inv_split_def] >>
  metis_tac[expr_body_pre_eval_mods]
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
  rpt strip_tac >> `src = NONE` by metis_tac[] >> gvs[] >>
  drule_then strip_assume_tac body_inv_main_code >>
  drule_then assume_tac body_inv_contract >> gvs[] >>
  metis_tac[SIMP_RULE (srw_ss()) [ALOOKUP_def]
    (Q.INST [`mods` |-> `[(NONE,tops)]`, `src` |-> `NONE`]
      body_inv_storage_var_types_mods)]
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


Theorem body_inv_mcopy:
  !tops ctx cenv cx. body_inv tops ctx cenv cx ==> cenv.ce_target CapMcopy
Proof
  metis_tac[body_inv_contract, body_inv_mcopy_mods]
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

Theorem body_tuple_target_toplevel_aligned_mods:
  contract_inv mods exps ctx cenv cx /\ ALOOKUP mods src = SOME tops /\
  expr_sim_inv_mods mods cenv cx env es /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  supported_scalar_target tops (NONE,id) /\ is_word_type ty /\
  type_place_target env (TopLevelNameTarget (src,id)) = SOME (Type ty) /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  tuple_target_aligned cenv cx (BaseTarget (TopLevelNameTarget (src,id))) ty tv
Proof
  strip_tac >>
  `get_module_code cx src = SOME tops` by metis_tac[contract_inv_module_codes] >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  `find_var_decl_by_name id tops <> NONE` by
    metis_tac[supported_scalar_target_decl, find_var_decl_storage_some] >>
  gvs[vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (drule_all env_assignable_find_NONE >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  drule_all_then strip_assume_tac contract_inv_variable_metadata >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  drule_all exprSimTopLevelPropsTheory.toplevel_storage_ce_vars >> strip_tac >>
  simp[tupleTargetStorePropsTheory.tuple_target_aligned_toplevel]
QED

Theorem body_tuple_target_field_aligned[local]:
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
  `src = NONE` by
    metis_tac[body_inv_toplevel_target_main,
      vyperTypeEnvTheory.type_place_target_AttributeTarget, optionTheory.IS_SOME_EXISTS] >>
  drule_all supported_storage_field_write_decl >> strip_tac >> gvs[] >>
  drule_then assume_tac body_inv_contract >>
  `!v m d i. MEM (VariableDecl v m id d i) tops ==>
     cenv.ce_module_var_type (NONE,id) = SOME d /\
     cenv.ce_hashmap_info (NONE,id) = NONE` by
    (rpt strip_tac >> metis_tac[SIMP_RULE (srw_ss()) [ALOOKUP_def]
      (Q.INST [`mods` |-> `[(NONE,tops)]`, `src` |-> `NONE`]
        contract_inv_variable_metadata)]) >>
  drule_then strip_assume_tac body_inv_main_code >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  gvs[vyperTypeEnvTheory.type_place_target_AttributeTarget,
      vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (drule_all env_assignable_find_NONE >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  rename1 `attribute_type _ tgt_ty fld = SOME _` >>
  `tgt_ty = StructT sid /\
   cenv.ce_module_var_type (NONE,id) = SOME (StructT sid) /\
   cenv.ce_hashmap_info (NONE,id) = NONE` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
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
   (?nsid dty. g = BaseTarget (TopLevelNameTarget nsid) /\
               supported_scalar_target tops nsid /\
               type_place_target env (TopLevelNameTarget nsid) = SOME (Type dty) /\
               is_word_type dty) \/
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
  >- (Cases_on `nsid` >> rename1 `(src,id)` >>
      `src = NONE` by metis_tac[body_inv_toplevel_target_main, optionTheory.IS_SOME_EXISTS] >>
      gvs[] >>
      drule_then strip_assume_tac body_inv_main_code >>
      drule_then assume_tac body_inv_contract >>
      fs[expr_sim_inv_split_def] >>
      irule (SIMP_RULE (srw_ss()) [ALOOKUP_def]
        (Q.INST [`mods` |-> `[(NONE,tops)]`, `src` |-> `NONE`, `exps` |-> `[]`]
          body_tuple_target_toplevel_aligned_mods)) >> simp[] >> metis_tac[])
  >- simp[tupleTargetStorePropsTheory.tuple_target_layout_def]
  >- (irule body_tuple_target_field_aligned >> metis_tac[])
  >> simp[tupleTargetStorePropsTheory.tuple_target_layout_def]
QED

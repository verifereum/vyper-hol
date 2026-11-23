(* The top-level storage name reaches the expression cut with a literal
   operand and a root observation, before the iterator reads its length. *)
Theory forStorageLiteralCapture
Ancestors
  bodyInvCodeProps moduleVariableKeyProps
  bodyStorageMetadata
  bodyTypedTargetScope vyperTypeSystem
  bodySim exprBodyPreProps exprSimHypsDefs exprSimTopLevelProps stateRelProj
  gasOutcomeFull whitelistVisibility supportedExprForms
  vyperTypeEnv vyperTypeInvariants vyperTypeGlobalLookupSoundness vyperTypeValues
  vyperStoragePlaceRegion vyperStorageFootprint vyperInterpreter vyperState
  vyperLookupStorage vyperAST vyperValue
  exprLowering loweringStateRelDefs context compileEnv venomInst finite_map list

Theorem literal_storage_decl_mods[local]:
  contract_inv mods exps ctx c cx /\ ALOOKUP mods src = SOME tops /\
  supported_storage_value tops (NONE,name) ty ==>
  ?tr. get_module_code cx src = SOME tops /\
       find_var_decl_by_name name tops = SOME (StorageVarDecl tr ty,name)
Proof
  strip_tac >>
  drule_then (assume_tac o Q.SPEC `src`) contract_inv_module_codes >>
  drule_all_then assume_tac contract_inv_unqualified_variable_keys >>
  qpat_x_assum `supported_storage_value _ _ _` mp_tac >>
  simp[supported_storage_value_def] >>
  Cases_on `supported_variable_decl tops (NONE,name)` >> simp[] >>
  rename1 `supported_variable_decl _ _ = SOME info` >>
  PairCases_on `info` >> Cases_on `info1` >> Cases_on `info3` >> simp[] >>
  strip_tac >>
  drule supported_variable_decl_storage_binding >> disch_then drule >>
  simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem literal_storage_decl[local]:
  body_inv tops ctx c cx /\ FST nid = NONE /\ supported_storage_value tops nid ty ==>
  ?tr name. nid = (NONE,name) /\ get_module_code cx NONE = SOME tops /\
    find_var_decl_by_name name tops = SOME (StorageVarDecl tr ty,name)
Proof
  PairCases_on `nid` >> strip_tac >>
  gvs[] >> drule_then assume_tac body_inv_contract >>
  drule_all_then strip_assume_tac (SIMP_RULE (srw_ss()) [alistTheory.ALOOKUP_def]
    (Q.INST [`mods` |-> `[(NONE,tops)]`, `src` |-> `NONE`]
      literal_storage_decl_mods)) >>
  metis_tac[]
QED

Theorem for_storage_literal_capture:
  body_inv tops ctx c cx /\ supported_storage_value tops nid (ArrayT typ bd) /\
  expr_body_pre c cx env (TopLevelName (ArrayT typ bd) nid) es /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  compile_expr c (expr_type (TopLevelName (ArrayT typ bd) nid))
    (TopLevelName (ArrayT typ bd) nid) sa = (vv,se) /\
  (!tail. eval_expr cx (TopLevelName (ArrayT typ bd) nid)
      (es with gas_obs := obs ++ tail) = (INL rv,em with gas_obs := tail)) /\
  valid_horizon cx st0 H em.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func c cx es s0) ==>
  ?tr off. rv = PlaceR (StoragePlace tr (n2w off) (ArrayTV tyv bd)) /\
    vv_operand vv = Lit (n2w off) /\ se = sa /\
    MEM (StorageRoot tr off (ArrayTV tyv bd)) em.storage_trace /\
    storage_subregion (ArrayTV tyv bd) [] 0 (ArrayTV tyv bd)
Proof
  strip_tac >>
  drule_then strip_assume_tac expr_body_pre_static_facts >>
  `FST nid = NONE` by
    (PairCases_on `nid` >> gvs[] >> metis_tac[body_inv_toplevel_read_main]) >>
  drule_all_then strip_assume_tac literal_storage_decl >> gvs[] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  drule_all_then strip_assume_tac TopLevelName_toplevel_vtypes_Type >>
  `FLOOKUP env.bare_globals (NONE,name) = NONE` by
    (Cases_on `FLOOKUP env.bare_globals (NONE,name)` >> simp[] >>
     drule_all_then strip_assume_tac env_consistent_bare_global_find_NONE >> gvs[]) >>
  `?off tv. lookup_var_slot_from_layout cx tr NONE name = SOME off /\
            evaluate_type (get_tenv cx) (ArrayT typ bd) = SOME tv` by
    (drule_all_then strip_assume_tac env_consistent_toplevel_storage_static >>
     gvs[optionTheory.IS_SOME_EXISTS]) >>
  drule_then strip_assume_tac evaluate_type_ArrayT_cases >> gvs[] >>
  qpat_x_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
  simp[Once evaluate_def, lookup_global_def, bind_def, ignore_bind_def,
       record_storage_event_def, lift_option_type_def, return_def, raise_def] >>
  strip_tac >>
  rename1 `evaluate_type (get_tenv cx) (ArrayT typ bd) = SOME (ArrayTV elem bd)` >>
  `em.storage_trace = es.storage_trace ++ [StorageRoot tr off (ArrayTV elem bd)]` by
    fs[evaluation_state_component_equality] >>
  `valid_horizon cx st0 H es.storage_trace` by metis_tac[valid_horizon_append] >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _`
    (qspec_then `H` (drule_then assume_tac)) >>
  drule_then strip_assume_tac stmt_state_rel_vars_rels >>
  drule_all_then strip_assume_tac toplevel_storage_ce_vars >>
  qexistsl [`tr`, `off`] >> simp[storage_subregion_def] >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  Cases_on `tr` >>
  simp[Once compile_expr_def, expr_type_def] >>
  strip_tac >> gvs[vv_operand_def, mk_ptr_def]
QED

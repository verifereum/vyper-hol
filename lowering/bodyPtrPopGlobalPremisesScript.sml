Theory bodyPtrPopGlobalPremises
Ancestors
  bodyPtrPopGlobalSource vyperTypeStoragePreservation
  compileVyper bodyPtrPopGlobalLoweringInputs vyperState vyperStorageBackend
  bodySim bodyPtrPopGlobalLegality bodyPtrPopGlobalUnit
  bodyPtrPopGlobalCompile vyperContext typedCopyDomain
  exprSimHypsDefs vyperTypeInvariants structFieldsProps placeTypingProps

Theorem pop_global_source_oracle_storage:
  oracle_storage_ok pop_global_cx pop_global_es
Proof
  simp[oracle_storage_ok_def, pop_global_es_def, set_storage_def,
       empty_state_def]
QED

Theorem pop_global_source_tenv:
  get_tenv pop_global_cx = type_env pop_global_tops
Proof
  EVAL_TAC >> simp[]
QED

Theorem pop_global_source_metadata_acyclic:
  acyclic_struct_metadata (make_struct_fields_map pop_global_tops)
Proof
  EVAL_TAC >> simp[]
QED

Theorem pop_global_source_body_inv:
  body_inv pop_global_tops pop_global_runtime_context
    pop_global_package_env pop_global_cx
Proof
  simp[body_inv_def, pop_global_supported, pop_global_source_module,
       pop_global_package_env_def, build_compile_env_ce_func_ids,
       build_compile_env_ce_func_info, build_compile_env_ce_func_param_types,
       build_compile_env_ce_func_return_type, build_compile_env_ce_struct_fields] >>
  conj_tac >-
   (qexistsl_tac [`pop_global_policy`,
      `<|cu_context := pop_global_runtime_context; cu_data_segment := []|>`] >>
    simp[pop_global_unit_lowered, pop_global_policy_resolved, pop_global_cx_def,
         empty_evaluation_context_def]) >>
  simp[pop_global_source_tenv, pop_global_source_metadata_acyclic,
       pop_global_cx_def, empty_evaluation_context_def] >>
  simp[build_compile_env_def] >>
  EVAL_TAC >> simp[]
QED

Theorem pop_global_source_empty_local_maps:
  pop_global_env.var_types = FEMPTY /\
  pop_global_env.bare_globals = FEMPTY /\
  pop_global_es.outcomes = SOME [] /\ pop_global_es.scopes = [FEMPTY]
Proof
  EVAL_TAC
QED

Theorem pop_global_source_expr_inv:
  expr_sim_inv pop_global_package_env pop_global_cx pop_global_env pop_global_es
Proof
  simp[expr_sim_inv_def, pop_global_source_env_consistent,
       pop_global_source_state_typed, pop_global_source_accounts_typed,
       pop_global_source_context_typed, pop_global_source_functions_typed,
       pop_global_source_storage_well_formed, pop_global_source_layout_safe,
       pop_global_source_oracle_storage,
       pop_global_source_empty_local_maps, pop_global_source_module_cases,
       pop_global_source_tenv, outcomes_accounts_typed_def, popped_keys_indexed_def] >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> simp[] >> rpt strip_tac >> gvs[]) >>
  conj_tac >-
   (simp[pop_global_package_env_def, build_compile_env_ce_struct_fields] >>
    irule make_struct_fields_map_consistent >> EVAL_TAC) >>
  conj_tac >-
   (EVAL_TAC >> rpt strip_tac >> gvs[] >>
    EVAL_TAC >> simp[SF wordsLib.SIZES_ss] >> rpt strip_tac >> gvs[] >>
    EVAL_TAC) >>
  conj_tac >-
   (EVAL_TAC >> rpt strip_tac >>
    Cases_on `id = "A"` >> Cases_on `id = "B"` >> gvs[] >> EVAL_TAC) >>
  simp[place_map_tables_agree_on_defined_def] >>
  EVAL_TAC >> rpt strip_tac >>
  PairCases_on `nsid` >>
  Cases_on `nsid0 = NONE` >> Cases_on `nsid1 = "A"` >>
  Cases_on `nsid1 = "B"` >> gvs[] >> EVAL_TAC
QED

Theorem pop_global_source_expr_pre:
  expr_body_pre pop_global_package_env pop_global_cx pop_global_env
    (Pop (BaseT (UintT 256)) pop_global_target) pop_global_es
Proof
  simp[expr_body_pre_def, pop_global_source_expr_inv,
       pop_global_expr_typing, pop_global_source_tenv] >>
  conj_tac >- (EVAL_TAC) >>
  conj_tac >- (EVAL_TAC) >>
  conj_tac >-
   (CONV_TAC (RAND_CONV EVAL) >>
    MATCH_ACCEPT_TAC pop_global_source_call_safe) >>
  conj_tac >- EVAL_TAC >>
  conj_tac >-
   (CONV_TAC (RAND_CONV EVAL) >>
    simp[pop_global_source_module, pop_global_supported]) >>
  EVAL_TAC >> simp[]
QED

Theory bodyPtrPopFullFrameSource
Ancestors
  bodyPtrPopFullFrameContext bodyPtrPopFullFrameProbe vyperTypeInvariants vyperTypeStoragePreservation
  vyperState vyperStorageBackend vyperStorageLayoutSafety vyperLookupStorage
  vyperContext vyperValue vyperInterpreter vyperTypeContract
  exprSimHypsDefs structFieldsProps placeTypingProps

Theorem pop_full_frame_scopes:
  env_scopes_consistent pop_full_frame_env pop_full_frame_cx pop_full_frame_es
Proof
  EVAL_TAC >> simp[]
QED

Theorem pop_full_frame_immutables:
  env_immutables_consistent pop_full_frame_env pop_full_frame_cx pop_full_frame_es
Proof
  EVAL_TAC >> rpt strip_tac >>
  Cases_on `id = "a"` >> gvs[] >> gvs[find_var_decl_by_name_def]
QED

Theorem pop_full_frame_env_consistent:
  env_consistent pop_full_frame_env pop_full_frame_cx pop_full_frame_es
Proof
  simp[env_consistent_def, pop_full_frame_env_context,
       pop_full_frame_scopes, pop_full_frame_immutables]
QED

Theorem pop_full_frame_state_typed:
  state_well_typed pop_full_frame_es
Proof
  EVAL_TAC >> simp[]
QED

Theorem pop_full_frame_accounts_typed:
  accounts_well_typed pop_full_frame_es.accounts
Proof
  EVAL_TAC >> gen_tac >> Cases_on `addr = 0w` >> simp[]
QED

Theorem pop_full_frame_storage_info:
  storage_var_info pop_full_frame_cx mid n = SOME (b,off,tv) <=>
  mid = NONE /\ n = "a" /\ b = F /\ off = 0 /\
  tv = ArrayTV (BaseTV (UintT 256)) (Dynamic 2)
Proof
  Cases_on `mid` >> EVAL_TAC >>
  Cases_on `n = "a"` >> gvs[] >> EVAL_TAC >> simp[SF wordsLib.SIZES_ss] >> EVAL_TAC >> simp[] >> metis_tac[]
QED

Theorem pop_full_frame_storage_regions:
  declared_storage_region pop_full_frame_cx mid n subs = SOME (b,slot,tv) <=>
  mid = NONE /\ n = "a" /\ b = F /\ subs = [] /\ slot = 0w /\
  tv = ArrayTV (BaseTV (UintT 256)) (Dynamic 2)
Proof
  Cases_on `mid` >> EVAL_TAC >>
  Cases_on `n = "a"` >> simp[] >> Cases_on `subs = []` >> gvs[] >>
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss] >> EVAL_TAC >> simp[] >> metis_tac[]
QED

Theorem pop_full_frame_layout_safe:
  storage_layout_safe pop_full_frame_cx
Proof
  simp[storage_layout_safe_def, well_formed_layout_def,
       pop_full_frame_storage_info, pop_full_frame_storage_regions,
       nonreentrant_slot_separated_def, pop_full_frame_cx_def,
       empty_evaluation_context_def] >>
  rpt strip_tac >> gvs[] >> EVAL_TAC >> simp[]
QED

Theorem pop_full_frame_slots:
  slots_in_range pop_full_frame_storage 0
    (ArrayTV (BaseTV (UintT 256)) (Dynamic 2))
Proof
  EVAL_TAC >> simp[]
QED

Theorem pop_full_frame_backend:
  get_storage_backend pop_full_frame_cx F pop_full_frame_es =
    (INL pop_full_frame_storage,pop_full_frame_es)
Proof
  simp[pop_full_frame_es_def, get_storage_backend_eq, get_storage_after_set]
QED

Theorem pop_full_frame_storage_well_formed:
  contract_storage_well_formed pop_full_frame_cx pop_full_frame_es
Proof
  simp[contract_storage_well_formed_def, well_formed_storage_def,
       storage_var_in_range_def, pop_full_frame_storage_info,
       pop_full_frame_storage_regions] >>
  rpt strip_tac >> gvs[pop_full_frame_backend] >> simp[pop_full_frame_slots]
QED

Theorem pop_full_frame_oracle_storage:
  oracle_storage_ok pop_full_frame_cx pop_full_frame_es
Proof
  simp[oracle_storage_ok_def, pop_full_frame_es_def, set_storage_def,
       empty_state_def]
QED

Theorem pop_full_frame_context_typed:
  context_well_typed pop_full_frame_cx
Proof
  EVAL_TAC >> simp[]
QED

Theorem pop_full_frame_empty_local_maps:
  pop_full_frame_env.var_types = FEMPTY /\
  pop_full_frame_env.bare_globals = FEMPTY /\
  pop_full_frame_es.outcomes = SOME [] /\ pop_full_frame_es.scopes = [FEMPTY]
Proof
  EVAL_TAC
QED

Theorem pop_full_frame_expr_inv:
  expr_sim_inv pop_full_frame_body_env pop_full_frame_cx
    pop_full_frame_env pop_full_frame_es
Proof
  simp[expr_sim_inv_def, pop_full_frame_env_consistent,
       pop_full_frame_state_typed, pop_full_frame_accounts_typed,
       pop_full_frame_context_typed, pop_full_frame_functions_typed,
       pop_full_frame_storage_well_formed, pop_full_frame_layout_safe,
       pop_full_frame_oracle_storage, pop_full_frame_empty_local_maps,
       pop_full_frame_tenv, outcomes_accounts_typed_def, popped_keys_indexed_def] >>
  conj_tac >- (EVAL_TAC >> simp[] >> rpt strip_tac >> gvs[lookup_flag_def]) >>
  conj_tac >- (EVAL_TAC >> simp[] >> rpt strip_tac >> gvs[]) >>
  conj_tac >-
   (simp[pop_full_frame_body_env_def, pop_full_frame_cenv_def,
         compileVyperTheory.build_compile_env_ce_struct_fields] >>
    irule make_struct_fields_map_consistent >> EVAL_TAC) >>
  conj_tac >-
   (EVAL_TAC >> rpt strip_tac >> gvs[]) >>
  conj_tac >-
   (EVAL_TAC >> rpt strip_tac >> Cases_on `id = "a"` >> gvs[find_var_decl_by_name_def] >> EVAL_TAC) >>
  simp[place_map_tables_agree_on_defined_def] >>
  EVAL_TAC >> rpt strip_tac >> PairCases_on `nsid` >>
  Cases_on `nsid0 = NONE` >> Cases_on `nsid1 = "a"` >> gvs[] >> EVAL_TAC
QED

Theorem pop_full_frame_expr_pre:
  expr_body_pre pop_full_frame_body_env pop_full_frame_cx
    pop_full_frame_env pop_full_frame_expr pop_full_frame_es
Proof
  simp[expr_body_pre_def, pop_full_frame_expr_inv] >>
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss] >> EVAL_TAC >>
  qexists `[]` >>
  conj_tac >-
   (simp[relationTheory.irreflexive_def] >> gen_tac >> strip_tac >>
    drule relationTheory.TC_CASES1_E >>
    simp[vyperTypeCallGraphSoundnessTheory.call_edge_rel_def]) >>
  rpt strip_tac >> Cases_on `fn = "take"` >> gvs[] >> EVAL_TAC
QED

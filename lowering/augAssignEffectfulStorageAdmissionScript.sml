(* Concrete declared-region admission, separate from compiler witnesses. *)
Theory augAssignEffectfulStorageAdmission
Ancestors
  augAssignEffectfulSourceWitness vyperStorageLayoutSafety exprStoragePreservation
  vyperStorageBackend vyperContext vyperState vyperLookupStorage
  vyperTypeStoragePreservation vfmState

Theorem effaug_declared_region:
  declared_storage_region effaug_cx mid n subs = SOME (b,slot,tv) ==>
  mid = NONE /\ n = "a" /\ subs = [] /\ b = F /\ slot = 0w /\
  tv = ArrayTV (ArrayTV (BaseTV (UintT 8)) (Fixed 1)) (Dynamic 1)
Proof
  simp[declared_storage_region_def, get_module_code_def, effaug_cx_def,
       empty_evaluation_context_def, empty_call_txn_def] >>
  Cases_on `mid` >> simp[] >>
  simp[effaug_tops_def, find_var_decl_by_name_def] >>
  Cases_on `n = "a"` >> simp[] >>
  Cases_on `subs = []` >> simp[] >>
  CONV_TAC computeLib.EVAL_CONV >>
  simp[vyperValueTheory.type_slot_size_def, SF wordsLib.SIZES_ss] >>
  rpt strip_tac >> gvs[]
QED

Theorem effaug_storage_info:
  storage_var_info effaug_cx mid n = SOME (b,off,tv) ==>
  mid = NONE /\ n = "a" /\ b = F /\ off = 0 /\
  tv = ArrayTV (ArrayTV (BaseTV (UintT 8)) (Fixed 1)) (Dynamic 1)
Proof
  strip_tac >>
  drule declared_storage_region_ordinary >>
  disch_then (mp_tac o MATCH_MP effaug_declared_region) >>
  strip_tac >> gvs[] >>
  qpat_x_assum `_ = storage_var_info _ _ _` mp_tac >>
  EVAL_TAC >>
  simp[vyperValueTheory.type_slot_size_def, SF wordsLib.SIZES_ss]
QED

Theorem effaug_initial_range:
  slots_in_range (update_storage 0w 1w (\k. 0w)) 0
    (ArrayTV (ArrayTV (BaseTV (UintT 8)) (Fixed 1)) (Dynamic 1))
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss] >> EVAL_TAC
QED

Theorem effaug_contract_from_range:
  slots_in_range (get_storage effaug_cx st F) 0
    (ArrayTV (ArrayTV (BaseTV (UintT 8)) (Fixed 1)) (Dynamic 1)) ==>
  contract_storage_well_formed effaug_cx st
Proof
  strip_tac >>
  simp[contract_storage_well_formed_def, well_formed_storage_def,
       storage_var_in_range_def, get_storage_backend_eq] >>
  conj_tac >> rpt gen_tac >> strip_tac
  >- (drule effaug_storage_info >> strip_tac >> gvs[]) >>
  drule effaug_declared_region >> strip_tac >> gvs[]
QED

Theorem effaug_initial_contract_storage:
  contract_storage_well_formed effaug_cx effaug_es
Proof
  irule effaug_contract_from_range >>
  simp[vyperStorageBackendTheory.get_storage_def, effaug_cx_def, effaug_es_def,
       empty_evaluation_context_def, empty_call_txn_def, effaug_accounts_def,
       lookup_account_def, combinTheory.APPLY_UPDATE_THM, effaug_initial_range]
QED

Theorem effaug_post_contract_storage:
  contract_storage_well_formed effaug_cx (effaug_post obs)
Proof
  irule effaug_contract_from_range >>
  simp[effaug_post_storage,
       augAssignEffectfulOutcomeProbeTheory.empty_outer_array_noncanonical_payload]
QED

Theorem effaug_oracle_storage:
  oracle_storage_ok effaug_cx effaug_es
Proof
  simp[oracle_storage_ok_def, effaug_es_def, empty_state_def] >>
  irule contract_storage_well_formed_storage_frame >>
  qexists_tac `effaug_post []` >>
  simp[effaug_post_contract_storage, effaug_post_def,
       vyperStorageBackendTheory.get_storage_def] >>
  Cases >> simp[vyperStorageBackendTheory.get_storage_def]
QED

Theorem effaug_layout_safe:
  storage_layout_safe effaug_cx
Proof
  simp[storage_layout_safe_def, well_formed_layout_def] >>
  rpt conj_tac
  >- (rpt strip_tac >> drule effaug_storage_info >> strip_tac >>
      gvs[vyperValueTheory.type_slot_size_def, SF wordsLib.SIZES_ss])
  >- (rpt strip_tac >> imp_res_tac effaug_storage_info >> gvs[])
  >- (rpt strip_tac >> drule effaug_declared_region >> strip_tac >>
      gvs[vyperValueTheory.type_slot_size_def, SF wordsLib.SIZES_ss])
  >- (rpt strip_tac >> imp_res_tac effaug_declared_region >> gvs[]) >>
  simp[nonreentrant_slot_separated_def, effaug_cx_def,
       empty_evaluation_context_def]
QED

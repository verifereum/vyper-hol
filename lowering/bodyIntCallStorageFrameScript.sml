(* Reconstruct only live storage observations, not dead popped slots. *)
Theory bodyIntCallStorageFrame
Ancestors
  bodyIntCallSourceFrame loweringPosts accountsRelProps vyperStorageBackend
  vyperInterpreter vyperState

Theorem storage_holds_live_endpoint:
  storage_holds cx tr ty raw w es s0 /\
  (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
        storage_read_live cx tr (get_storage cx es tr) w tv) /\
  storage_agree (storage_dead cx tr (get_storage cx es tr))
    (get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s) ==>
  storage_holds cx tr ty raw w es s
Proof
  simp[storage_holds_def] >> rpt strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  irule storage_range_agree_of_live >> simp[] >>
  gvs[storage_range_agree_def] >> metis_tac[]
QED

Theorem storage_holds_outcomes:
  storage_holds cx tr ty raw w (es with <|outcomes := os; gas_obs := gs|>) s <=>
  storage_holds cx tr ty raw w es s
Proof
  Cases_on `tr` >>
  simp[storage_holds_def, read_result_outcomes_iff,
       read_storage_slot_eq, get_storage_def, AllCaseEqs()]
QED

Theorem storage_holds_live_endpoint_outcomes:
  storage_holds cx tr ty raw w es s0 /\
  (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
        storage_read_live cx tr (get_storage cx es tr) w tv) /\
  storage_agree (storage_dead cx tr (get_storage cx es tr))
    (get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s) ==>
  storage_holds cx tr ty raw w (es with <|outcomes := os; gas_obs := gs|>) s
Proof
  simp[storage_holds_outcomes] >> metis_tac[storage_holds_live_endpoint]
QED

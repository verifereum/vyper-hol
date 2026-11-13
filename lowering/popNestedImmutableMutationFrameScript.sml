(* A place mutation cannot alter an immutable lookup at another root. *)
Theory popNestedImmutableMutationFrame
Ancestors
  popNestedImmutableAccess vyperPlaceFrames vyperScopePreservation
  vyperPlaceMutationSoundness vyperStatePreservation
  vyperInterpreter vyperState vyperMisc finite_map alist list

val query = ``\cx src id (st:evaluation_state).
  FLOOKUP (case ALOOKUP st.immutables cx.txn.target of
    NONE => FEMPTY | SOME imms => get_source_immutables src imms) id``;

Theorem write_place_unwritten_immutable:
  (!path. p <> ImmutablePlace src id path) /\
  write_place cx p v st = (res,st') ==>
  ^query cx src id st' = ^query cx src id st
Proof
  Cases_on `p`
  >- (rpt strip_tac >> drule write_storage_place_immutables >> simp[])
  >- (rpt strip_tac >> drule write_memory_place_immutables >> simp[]) >>
  simp[write_place_def, bind_def, lift_option_type_def,
       lift_sum_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> imp_res_tac get_immutables_state >>
  gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.sum_CASE_rator,
      return_def, raise_def, AllCaseEqs()] >>
  metis_tac[set_immutable_unwritten_lookup]
QED

Theorem append_place_unwritten_immutable:
  (!path. p <> ImmutablePlace src id path) /\
  append_place cx p v st = (res,st') ==>
  ^query cx src id st' = ^query cx src id st
Proof
  Cases_on `p`
  >- (rpt strip_tac >> drule append_storage_place_scopes_immutables >> simp[]) >>
  simp[append_place_def, bind_def, lift_sum_def, AllCaseEqs()] >>
  rpt strip_tac >> imp_res_tac place_type_value_state >>
  imp_res_tac read_place_state >>
  gvs[vyperMiscTheory.sum_CASE_rator, return_def, raise_def, AllCaseEqs()] >>
  irule (BETA_RULE write_place_unwritten_immutable) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem pop_place_unwritten_immutable:
  (!path. p <> ImmutablePlace src id path) /\
  pop_place cx p st = (res,st') ==>
  ^query cx src id st' = ^query cx src id st
Proof
  Cases_on `p`
  >- (rpt strip_tac >> drule pop_storage_place_scopes_immutables >> simp[])
  >- (rpt strip_tac >> drule pop_memory_place_state_frame >>
      disch_then (mp_tac o Q.AP_TERM `\s:evaluation_state. s.immutables`) >>
      simp[]) >>
  simp[pop_place_def, bind_def, ignore_bind_def, lift_option_type_def,
       lift_sum_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> imp_res_tac get_immutables_state >>
  gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.sum_CASE_rator,
      return_def, raise_def, AllCaseEqs()] >>
  metis_tac[set_immutable_unwritten_lookup]
QED

(*
 * State-update preservation lemmas for the fresh Vyper type system.
 *)

Theory vyperTypeStatePreservation
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage vyperTyping
  vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeValues
  vyperTypeEnv vyperTypeExprSoundness
Libs
  wordsLib

(* ===== Scope operations ===== *)

Theorem push_scope_preserves_state_well_typed:
  state_well_typed st /\ push_scope st = (INL u, st') ==>
  state_well_typed st'
Proof
  rw[push_scope_def, return_def, state_well_typed_def, scope_well_typed_def] >>
  rw[] >> rw[scope_well_typed_def]
QED

Theorem pop_scope_preserves_state_well_typed:
  state_well_typed st /\ pop_scope st = (INL u, st') ==>
  state_well_typed st'
Proof
  Cases_on `st.scopes` >>
  rw[pop_scope_def, return_def, raise_def, state_well_typed_def] >>
  rw[]
QED

Theorem push_scope_with_var_preserves_state_well_typed:
  state_well_typed st /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ push_scope_with_var id tv v st = (INL u, st') ==>
  state_well_typed st'
Proof
  rw[push_scope_with_var_def, return_def, state_well_typed_def,
     scope_well_typed_def] >> rw[] >>
  rw[scope_well_typed_def] >> gvs[FLOOKUP_UPDATE] >>
  metis_tac[evaluate_type_well_formed_type_value]
QED

Theorem new_variable_preserves_state_well_typed:
  state_well_typed st /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ new_variable id tv v st = (INL u, st') ==>
  state_well_typed st'
Proof
  rw[new_variable_def, bind_def, ignore_bind_def, return_def, raise_def,
     get_scopes_def, set_scopes_def, type_check_def, AllCaseEqs(), LET_THM,
     state_well_typed_def, scope_well_typed_def, list_CASE_rator,
     assert_def] >> gvs[scope_well_typed_def, FLOOKUP_UPDATE] >>
  rw[] >> rw[] >>
  metis_tac[evaluate_type_well_formed_type_value]
QED

(* ===== Storage/account/immutable operations ===== *)

Theorem read_storage_slot_preserves_state_well_typed:
  state_well_typed st /\ read_storage_slot cx is_transient slot tv st = (INL v, st') ==>
  state_well_typed st'
Proof
  Cases_on `is_transient` >>
  rw[read_storage_slot_def, get_storage_backend_def, get_transient_storage_def,
     get_accounts_def, bind_def, return_def, raise_def, lift_option_def,
     AllCaseEqs(), option_CASE_rator] >> gvs[]
QED

Theorem assign_target_preserves_state_well_typed:
  state_well_typed st /\ context_well_typed cx /\ accounts_well_typed st.accounts /\
  target_runtime_typed env tgt ty gv /\ assign_operation_runtime_typed env ty op /\
  assign_target cx gv op st = (INL res, st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  cheat
QED

Theorem materialise_preserves_type:
  state_well_typed st /\ toplevel_value_typed tvl tv /\ well_formed_type_value tv /\
  materialise cx tvl st = (INL v, st') ==>
  state_well_typed st' /\ value_has_type tv v
Proof
  cheat
QED

Theorem get_Value_preserves_type:
  toplevel_value_typed (Value v) tv ==> value_has_type tv v
Proof
  simp[toplevel_value_typed_def]
QED

(* eval_for preservation depends on statement-list soundness and therefore lives
   in vyperTypeStmtSoundnessScript.sml to avoid a StatePreservation ->
   StmtSoundness -> StatePreservation cycle. *)

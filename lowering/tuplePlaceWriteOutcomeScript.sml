(* Exhaustive write coverage at the actual pointer endpoint. *)
Theory tuplePlaceWriteOutcome
Ancestors
  tuplePlaceSourceHead stmtSimAugAssignPlaceMemory bodyAugPlaceTarget
  vyperState vyperPlaceWriteSoundness vyperTypeExprSoundness vyperStorageBackend
  vyperTyping exprLoweringProps compileEnv

Theorem tuple_place_memory_write_result:
  write_place cx (MemoryPlace id path) v es = (res,ff) /\
  no_type_error_result res ==> res = INL ()
Proof
  simp[write_place_def, get_scopes_def, bind_def, ignore_bind_def,
       lift_option_type_def, type_check_def, assert_def, lift_sum_def,
       set_scopes_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `find_containing_scope id es.scopes` >>
  simp[return_def, raise_def, no_type_error_result_def] >>
  rename1 `SOME fc` >> PairCases_on `fc` >> Cases_on `fc2.assignable` >>
  gvs[assert_def, bind_def, ignore_bind_def, return_def, raise_def, set_scopes_def,
      replace_memory_entry_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[no_type_error_result_def] >>
  Cases_on `evaluate_subscripts fc2.type fc2.value path` >>
  gvs[return_def, raise_def] >>
  Cases_on `assign_subscripts fc2.type fc2.value path (Replace v)` >>
  gvs[return_def, raise_def] >>
  drule_all aug_place_replace_read_error >> gvs[]
QED

Theorem tuple_place_source_write_success:
  target_pre cenv cx env bt es /\ well_typed_target env bt ty /\
  call_evaluation_safe cx (int_calls_target bt) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  ~immutable_root cx bt /\ eval_target_place cx bt es = (INL p,ee) /\
  stmt_state_rel ctx func cenv cx ee s /\
  write_place cx p v ee = (res,ff) ==> res = INL ()
Proof
  strip_tac >> drule_all tuple_place_source_target_endpoint >> strip_tac >>
  `state_well_typed ee` by fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
  drule_all write_place_no_type_error >> strip_tac >>
  Cases_on `p`
  >- (`~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
      gvs[write_place_def, write_storage_slot_eq, AllCaseEqs(),
          no_type_error_result_def])
  >- metis_tac[tuple_place_memory_write_result]
  >> drule tuple_place_target_base_inversion >> strip_tac >>
  drule aug_place_base_immutable_origin >> simp[]
QED

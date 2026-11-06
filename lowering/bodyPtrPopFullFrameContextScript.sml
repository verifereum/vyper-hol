Theory bodyPtrPopFullFrameContext
Ancestors
  bodyPtrPopFullFrameProbe vyperContext vyperState vyperTypeInvariants
  vyperTypeContractFunction vyperTypeContractContext vyperValue
  vyperInterpreter vyperTypeContract vyperTypeSystem

Theorem pop_full_frame_contract_checked:
  check_contract F pop_full_frame_cx.layouts 0w [(NONE,pop_full_frame_tops)] =
    SOME (build_contract_type_artifact F [(NONE,pop_full_frame_tops)])
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC >> simp[]
QED

Theorem pop_full_frame_initial_functions:
  functions_well_typed pop_full_frame_cx <=>
  functions_well_typed (initial_evaluation_context pop_full_frame_cx.sources
    pop_full_frame_cx.layouts pop_full_frame_cx.txn NONE)
Proof
  pure_rewrite_tac[functions_well_typed_def] >>
  simp[pop_full_frame_cx_def, empty_evaluation_context_def,
       initial_evaluation_context_def, lookup_nonreentrant_slot_def,
       empty_call_txn_def] >>
  pure_rewrite_tac[fn_sigs_consistent_def, fn_sigs_declared_complete_def,
       toplevel_vtypes_complete_def, bare_globals_complete_def,
       bare_global_assignable_complete_def, flag_members_complete_def,
       well_formed_type_def, context_function_live_def,
       get_module_code_def, get_tenv_def] >> simp[]
QED

Theorem pop_full_frame_functions_typed:
  functions_well_typed pop_full_frame_cx
Proof
  rewrite_tac[pop_full_frame_initial_functions] >>
  irule check_contract_functions_well_typed_initial >>
  qexistsl [`0w`, `build_contract_type_artifact F [(NONE,pop_full_frame_tops)]`,
            `[(NONE,pop_full_frame_tops)]`] >>
  simp[pop_full_frame_contract_checked, pop_full_frame_cx_def,
       empty_evaluation_context_def, empty_call_txn_def]
QED

Theorem pop_full_frame_initial_context:
  pop_full_frame_cx = (initial_evaluation_context pop_full_frame_cx.sources
    pop_full_frame_cx.layouts pop_full_frame_cx.txn NONE) with stk := [(NONE,"take")]
Proof
  EVAL_TAC >> simp[]
QED

Theorem pop_full_frame_artifact_env:
  pop_full_frame_env = artifact_env
    (build_contract_type_artifact F [(NONE,pop_full_frame_tops)])
    [(NONE,pop_full_frame_tops)] NONE
Proof
  EVAL_TAC >> simp[]
QED

Theorem pop_full_frame_env_context:
  env_context_consistent pop_full_frame_env pop_full_frame_cx
Proof
  once_rewrite_tac[pop_full_frame_initial_context] >>
  rewrite_tac[pop_full_frame_artifact_env] >>
  irule check_contract_env_context_consistent_initial_with_current_src >>
  qexists `0w` >>
  simp[pop_full_frame_contract_checked, pop_full_frame_cx_def,
       empty_evaluation_context_def, empty_call_txn_def]
QED

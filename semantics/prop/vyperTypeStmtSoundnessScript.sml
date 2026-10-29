(*
 * Statement and statement-list type-soundness corollaries for the executable
 * Vyper type system.
 *
 * The main mutual evaluator soundness proof lives in vyperTypeEvalSoundness;
 * this theory exposes the statement/list/function-body consequences.
 *)

Theory vyperTypeStmtSoundness
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair sum
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage vyperTyping
  vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeInvariants vyperTypeValues
  vyperTypeEnv vyperTypeEnvExtension vyperTypeEnvPreservation vyperTypeScopePop
  vyperTypeABI vyperTypeBindArguments vyperTypeExprResult vyperTypeStmtResult
  vyperTypeExtCallSoundness vyperTypeGlobalLookupSoundness vyperTypeAssignContext vyperTypeBuiltins vyperTypeExprSoundness vyperTypeAssignSoundness
  vyperExprNoControl vyperScopePreservation vyperEvalPreservesScopes
  vyperEvalMisc vyperStatePreservation vyperAssignPreservesType vyperTypeStatePreservation
  vyperTypeEvalSoundness
Libs
  wordsLib markerLib intLib

(* ===== Statement/list corollaries of eval_scc_type_sound_mutual ===== *)

Theorem eval_stmt_type_preservation_success:
  type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_stmt s) /\
  eval_stmt cx s st = (INL u, st') ==>
  state_well_typed st' /\ env_consistent env' cx st' /\ accounts_well_typed st'.accounts
Proof
  strip_tac >>
  drule_all (cj 1 eval_scc_type_sound_mutual) >>
  simp[]
QED

Theorem eval_stmts_no_type_error:
  type_stmts env ret_ty ss = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_stmts ss) ==>
  no_type_error_eval (eval_stmts cx ss st)
Proof
  strip_tac >>
  Cases_on `eval_stmts cx ss st` >>
  simp[no_type_error_eval_def] >>
  drule_all (cj 2 eval_scc_type_sound_mutual) >> rw[]
QED

Theorem eval_stmts_type_preservation_success:
  type_stmts env ret_ty ss = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_stmts ss) /\
  eval_stmts cx ss st = (INL u, st') ==>
  state_well_typed st' /\ env_consistent env' cx st' /\ accounts_well_typed st'.accounts
Proof
  strip_tac >>
  drule_all (cj 2 eval_scc_type_sound_mutual) >>
  simp[]
QED

Theorem eval_stmts_type_preservation_exception:
  type_stmts env ret_ty ss = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_stmts ss) /\
  eval_stmts cx ss st = (INR exn, st') ==>
  state_well_typed st' /\ stmt_error_ok env ret_ty (INR exn)
Proof
  strip_tac >>
  drule_all (cj 2 eval_scc_type_sound_mutual) >>
  simp[stmt_error_ok_def, no_type_error_result_def] >> strip_tac >>
  gvs[env_extends_def, return_exception_typed_def,
      value_runtime_typed_def]
QED

Theorem eval_stmts_preserves_state_and_accounts_well_typed:
  type_stmts env ret_ty ss = SOME env' /\ env_consistent env cx st /\
  state_well_typed st /\ context_well_typed cx /\
  accounts_well_typed st.accounts /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_stmts ss) /\
  eval_stmts cx ss st = (res,st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  strip_tac >>
  drule_all (cj 2 eval_scc_type_sound_mutual) >>
  simp[]
QED

(* ===== Top-level theorem shape ===== *)

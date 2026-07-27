(*
 * Public type-soundness theorem package.
 *
 * This theory is the single type-soundness ancestor intended for top-level
 * roll-up theories.  It owns short consumer-friendly typed-expression and
 * typed-statement wrappers, and imports the initial-state and checked-contract
 * soundness theories that own the larger setup/deployment/call theorems.
 *)

Theory vyperTypeSoundness
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage vyperTyping
  vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeInvariants vyperTypeValues
  vyperTypeEnv vyperTypeBuiltins vyperTypeExprSoundness
  vyperTypeEvalSoundness vyperTypeStatePreservation vyperTypeStmtSoundness
  vyperTypeCallSoundness vyperTypeInitialState vyperTypeContractSoundness
  vyperTypeStoragePreservation vyperTypeEvalStoragePreservation
Libs
  wordsLib

(* ===== Main no-TypeError theorem for already-typed statement lists ===== *)

Theorem typed_stmts_no_type_error:
  functions_well_typed cx /\ context_well_typed cx /\ accounts_well_typed st.accounts /\
  state_well_typed st /\ env_consistent env cx st /\
  call_evaluation_safe cx (int_calls_stmts ss) /\
  type_stmts env ret_ty ss = SOME env_after ==>
  no_type_error_eval (eval_stmts cx ss st)
Proof
  metis_tac[eval_stmts_no_type_error]
QED

Theorem typed_stmts_success_preserves_state_env:
  functions_well_typed cx /\ context_well_typed cx /\ accounts_well_typed st.accounts /\
  state_well_typed st /\ env_consistent env cx st /\
  call_evaluation_safe cx (int_calls_stmts ss) /\
  type_stmts env ret_ty ss = SOME env_after /\
  eval_stmts cx ss st = (INL u, st') ==>
  state_well_typed st' /\ env_consistent env_after cx st'
Proof
  metis_tac[eval_stmts_type_preservation_success]
QED

Theorem typed_stmts_exception_preserves_state_and_return_type:
  functions_well_typed cx /\ context_well_typed cx /\ accounts_well_typed st.accounts /\
  state_well_typed st /\ env_consistent env cx st /\
  call_evaluation_safe cx (int_calls_stmts ss) /\
  type_stmts env ret_ty ss = SOME env_after /\
  eval_stmts cx ss st = (INR exn, st') ==>
  state_well_typed st' /\ stmt_error_ok env ret_ty (INR exn)
Proof
  metis_tac[eval_stmts_type_preservation_exception]
QED

(* ===== Public expression theorem variants ===== *)

Theorem typed_expr_no_type_error:
  well_typed_expr env e /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr e) ==>
  no_type_error_eval (eval_expr cx e st)
Proof
  strip_tac >>
  Cases_on `eval_expr cx e st` >>
  simp[no_type_error_eval_def, no_type_error_result_def] >>
  drule_at(Pat`eval_expr`)(cj 8 eval_all_type_sound_mutual) >>
  disch_then drule >> simp[] >>
  rpt strip_tac >> gvs[no_type_error_result_def]
QED

Theorem typed_expr_success_preserves_type:
  well_typed_expr env e /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr e) /\
  eval_expr cx e st = (INL tvl, st') ==>
  state_well_typed st' /\ expr_runtime_typed env e tvl
Proof
  strip_tac >>
  drule_all (cj 8 eval_all_type_sound_mutual) >>
  strip_tac >> gvs[] >>
  metis_tac[expr_result_typed_runtime_typed]
QED

(* ===== Callable-function theorem shape ===== *)

Theorem typed_callable_body_no_type_error:
  functions_well_typed cx /\ context_well_typed cx /\ accounts_well_typed st.accounts /\
  state_well_typed st /\ env_consistent env_body cx st /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (fm,nr,args,dflts,ret,fn_body) /\
  call_evaluation_safe cx (int_calls_stmts fn_body) /\
  type_stmts env_body ret fn_body = SOME env_after ==>
  no_type_error_eval (eval_stmts cx fn_body st)
Proof
  metis_tac[eval_stmts_no_type_error]
QED


(* ===== Additive runtime/storage preservation API =====
 *
 * These results leave the established runtime and type-soundness predicates
 * unchanged.  External calls are admitted only through the exact protected
 * caller storage condition, which covers every successful or reverted result
 * and both persistent and transient storage.
 *)

Theorem typed_stmt_preserves_runtime_storage:
  type_stmt env ret_ty s = SOME env' /\
  runtime_storage_consistent env cx st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_stmt s) /\
  protected_storage_calls_preserve cx /\
  eval_stmt cx s st = (res,st') ==>
  no_type_error_result res /\
  case res of
  | INL _ => runtime_storage_consistent env' cx st'
  | INR exn => runtime_storage_consistent env cx st' /\
               return_exception_typed env ret_ty exn
Proof
  rpt strip_tac >>
  `contract_storage_well_formed cx st'` by
    metis_tac[eval_stmt_preserves_contract_storage_well_formed] >>
  fs[runtime_storage_consistent_def, runtime_consistent_def] >>
  drule_all (cj 1 eval_all_type_sound_mutual) >>
  Cases_on `res` >>
  gvs[runtime_storage_consistent_def, runtime_consistent_def]
QED

Theorem typed_stmts_preserve_runtime_storage:
  type_stmts env ret_ty ss = SOME env' /\
  runtime_storage_consistent env cx st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_stmts ss) /\
  protected_storage_calls_preserve cx /\
  eval_stmts cx ss st = (res,st') ==>
  no_type_error_result res /\
  case res of
  | INL _ => runtime_storage_consistent env' cx st'
  | INR exn => ?env_exn.
      env_extends env env_exn /\
      runtime_storage_consistent env_exn cx st' /\
      return_exception_typed env_exn ret_ty exn
Proof
  rpt strip_tac >>
  `contract_storage_well_formed cx st'` by
    metis_tac[eval_stmts_preserves_contract_storage_well_formed] >>
  fs[runtime_storage_consistent_def, runtime_consistent_def] >>
  drule_all (cj 2 eval_all_type_sound_mutual) >>
  Cases_on `res` >>
  gvs[runtime_storage_consistent_def, runtime_consistent_def] >>
  metis_tac[]
QED

Theorem typed_expr_preserves_runtime_storage:
  well_typed_expr env e /\
  runtime_storage_consistent env cx st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr e) /\
  protected_storage_calls_preserve cx /\
  eval_expr cx e st = (res,st') ==>
  runtime_storage_consistent env cx st' /\
  no_type_error_result res /\
  case res of
  | INL tv => expr_result_typed env e tv
  | INR _ => T
Proof
  rpt strip_tac >>
  `contract_storage_well_formed cx st'` by
    metis_tac[eval_expr_preserves_contract_storage_well_formed] >>
  fs[runtime_storage_consistent_def, runtime_consistent_def] >>
  drule_all (cj 8 eval_all_type_sound_mutual) >>
  gvs[runtime_storage_consistent_def, runtime_consistent_def]
QED

Theorem typed_exprs_preserve_runtime_storage:
  well_typed_exprs env es /\
  runtime_storage_consistent env cx st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_exprs es) /\
  protected_storage_calls_preserve cx /\
  eval_exprs cx es st = (res,st') ==>
  runtime_storage_consistent env cx st' /\
  no_type_error_result res /\
  case res of
  | INL vs => exprs_runtime_typed env es vs
  | INR _ => T
Proof
  rpt strip_tac >>
  `contract_storage_well_formed cx st'` by
    metis_tac[eval_exprs_preserves_contract_storage_well_formed] >>
  fs[runtime_storage_consistent_def, runtime_consistent_def] >>
  drule_all (cj 9 eval_all_type_sound_mutual) >>
  gvs[runtime_storage_consistent_def, runtime_consistent_def]
QED

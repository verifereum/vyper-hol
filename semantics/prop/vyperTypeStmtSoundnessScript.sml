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
  vyperAssignTarget vyperExprNoControl vyperScopePreservation vyperEvalPreservesScopes
  vyperEvalMisc vyperStatePreservation vyperAssignPreservesType vyperTypeStatePreservation
  vyperTypeEvalSoundness
Libs
  wordsLib markerLib intLib

(* ===== Statement/list corollaries of eval_all_type_sound_mutual ===== *)

Theorem eval_stmt_no_type_error:
  type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx ==>
  no_type_error_eval (eval_stmt cx s st)
Proof
  strip_tac >>
  Cases_on `eval_stmt cx s st` >>
  simp[no_type_error_eval_def] >>
  drule_all (cj 1 eval_all_type_sound_mutual) >> rw[]
QED

Theorem eval_stmt_type_preservation_success:
  type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_stmt cx s st = (INL u, st') ==>
  state_well_typed st' /\ env_consistent env' cx st' /\ accounts_well_typed st'.accounts
Proof
  strip_tac >>
  drule_all (cj 1 eval_all_type_sound_mutual) >>
  simp[]
QED

Theorem eval_stmt_type_preservation_exception:
  type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_stmt cx s st = (INR exn, st') ==>
  state_well_typed st' /\ stmt_error_ok env ret_ty (INR exn) /\ accounts_well_typed st'.accounts
Proof
  rpt strip_tac >>
  drule_all (cj 1 eval_all_type_sound_mutual) >>
  simp[stmt_error_ok_def] >>
  simp[no_type_error_result_def]
QED

Theorem eval_stmt_type_preservation_exception_state:
  type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_stmt cx s st = (INR exn, st') ==>
  state_well_typed st'
Proof
  metis_tac[eval_stmt_type_preservation_exception]
QED

Theorem eval_stmt_type_preservation_exception_ok:
  type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_stmt cx s st = (INR exn, st') ==>
  stmt_error_ok env ret_ty (INR exn)
Proof
  metis_tac[eval_stmt_type_preservation_exception]
QED

Theorem stmt_error_ok_type_defs_eq:
  env1.type_defs = env2.type_defs ==>
  (stmt_error_ok env1 ret_ty r <=> stmt_error_ok env2 ret_ty r)
Proof
  Cases_on `r` >> simp[stmt_error_ok_def, return_exception_typed_def] >>
  Cases_on `y` >> simp[value_runtime_typed_def]
QED

Theorem type_stmt_preserves_stmt_error_ok:
  type_stmt env ret_ty s = SOME env1 /\ stmt_error_ok env1 ret_ty r ==>
  stmt_error_ok env ret_ty r
Proof
  strip_tac >>
  drule type_stmt_env_preserved_static >> strip_tac >>
  fs[stmt_error_ok_def, return_exception_typed_def, value_runtime_typed_def]
QED

Theorem eval_stmt_type_preservation_exception_state_pair:
  type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_stmt cx s st = (INR exn, st') ==>
  state_well_typed st' /\ stmt_error_ok env ret_ty (INR exn)
Proof
  metis_tac[eval_stmt_type_preservation_exception]
QED

Theorem eval_stmts_no_type_error:
  type_stmts env ret_ty ss = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx ==>
  no_type_error_eval (eval_stmts cx ss st)
Proof
  MAP_EVERY qid_spec_tac [`env'`, `st`, `env`, `ss`] >>
  Induct >>
  rw[Once evaluate_def, no_type_error_eval_def, no_type_error_result_def, return_def] >>
  (* cons case *)
  gvs[type_stmt_def, AllCaseEqs(), Once evaluate_def, bind_def, ignore_bind_def] >>
  Cases_on `eval_stmt cx h st` >> gvs[no_type_error_eval_def, no_type_error_result_def] >>
  Cases_on `q` >> gvs[no_type_error_eval_def, no_type_error_result_def]
  >- (
    drule_all eval_stmt_type_preservation_success >> strip_tac >>
    first_x_assum drule_all >> rw[no_type_error_eval_def, no_type_error_result_def]) >>
  drule_all eval_stmt_no_type_error >>
  gvs[no_type_error_eval_def, no_type_error_result_def]
QED

Theorem eval_stmts_type_preservation_success:
  type_stmts env ret_ty ss = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_stmts cx ss st = (INL u, st') ==>
  state_well_typed st' /\ env_consistent env' cx st' /\ accounts_well_typed st'.accounts
Proof
  MAP_EVERY qid_spec_tac [`env'`, `st'`, `u`, `st`, `env`, `ss`] >>
  Induct
  >- simp[Once evaluate_def, return_def, type_stmt_def] >>
  rpt gen_tac >> strip_tac >>
  (* cons case *)
  gvs[type_stmt_def, AllCaseEqs(), Once evaluate_def, bind_def, ignore_bind_def] >>
  Cases_on `eval_stmt cx h st` >> gvs[] >>
  drule_all eval_stmt_type_preservation_success >> strip_tac >>
  first_x_assum drule_all >> rw[]
QED

Theorem eval_stmts_type_preservation_exception:
  type_stmts env ret_ty ss = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_stmts cx ss st = (INR exn, st') ==>
  state_well_typed st' /\ stmt_error_ok env ret_ty (INR exn)
Proof
  MAP_EVERY qid_spec_tac [`env'`, `st'`, `exn`, `st`, `env`, `ss`] >>
  Induct >> simp[Once evaluate_def, return_def] >>
  simp[type_stmt_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >>
  reverse(gvs[bind_def, ignore_bind_def, AllCaseEqs()]) >- (
    drule_all eval_stmt_type_preservation_exception >> rw[] ) >>
  drule_all eval_stmt_type_preservation_success >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  gvs[] >>
  drule_all type_stmt_preserves_stmt_error_ok >>
  rw[]
QED

(* ===== Top-level theorem shape ===== *)

Theorem function_body_type_sound:
  functions_well_typed cx /\ context_well_typed cx /\ accounts_well_typed st.accounts /\
  state_well_typed st /\ env_consistent env cx st /\
  type_stmts env ret_ty body_stmts = SOME env_after ==>
  no_type_error_eval (eval_stmts cx body_stmts st)
Proof
  metis_tac[eval_stmts_no_type_error]
QED

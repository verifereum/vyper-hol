(*
 * Public fresh type-soundness theorem surface.
 *)

Theory vyperTypeSoundnessNew
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage vyperTyping
  vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeValues
  vyperTypeEnv vyperTypeBuiltins vyperTypeExprSoundness
  vyperTypeStatePreservation vyperTypeStmtSoundness vyperTypeCallSoundness
Libs
  wordsLib

(* ===== Main no-TypeError theorem for already-typed statement lists ===== *)

Theorem typed_stmts_no_type_error:
  functions_well_typed cx /\ context_well_typed cx /\ accounts_well_typed st.accounts /\
  state_well_typed st /\ env_consistent env cx st /\
  type_stmts env ret_ty ss = SOME env_after ==>
  no_type_error_eval (eval_stmts cx ss st)
Proof
  metis_tac[eval_stmts_no_type_error]
QED

Theorem typed_stmts_success_preserves_state_env:
  functions_well_typed cx /\ context_well_typed cx /\ accounts_well_typed st.accounts /\
  state_well_typed st /\ env_consistent env cx st /\
  type_stmts env ret_ty ss = SOME env_after /\
  eval_stmts cx ss st = (INL u, st') ==>
  state_well_typed st' /\ env_consistent env_after cx st'
Proof
  metis_tac[eval_stmts_type_preservation_success]
QED

Theorem typed_stmts_exception_preserves_state_and_return_type:
  functions_well_typed cx /\ context_well_typed cx /\ accounts_well_typed st.accounts /\
  state_well_typed st /\ env_consistent env cx st /\
  type_stmts env ret_ty ss = SOME env_after /\
  eval_stmts cx ss st = (INR exn, st') ==>
  state_well_typed st' /\ stmt_error_ok env ret_ty (INR exn)
Proof
  metis_tac[eval_stmts_type_preservation_exception]
QED

(* ===== Public expression theorem variants ===== *)

Theorem typed_expr_no_type_error:
  well_typed_expr env e /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx ==>
  no_type_error_eval (eval_expr cx e st)
Proof
  metis_tac[eval_expr_no_type_error]
QED

Theorem typed_expr_success_preserves_type:
  well_typed_expr env e /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_expr cx e st = (INL tvl, st') ==>
  state_well_typed st' /\ expr_runtime_typed env e tvl
Proof
  metis_tac[eval_expr_type_preservation]
QED

(* ===== Callable-function theorem shape ===== *)

Theorem typed_callable_body_no_type_error:
  functions_well_typed cx /\ context_well_typed cx /\ accounts_well_typed st.accounts /\
  state_well_typed st /\ env_consistent env_body cx st /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (fm,nr,args,dflts,ret,body) /\
  type_stmts env_body ret body = SOME env_after ==>
  no_type_error_eval (eval_stmts cx body st)
Proof
  metis_tac[eval_stmts_no_type_error]
QED

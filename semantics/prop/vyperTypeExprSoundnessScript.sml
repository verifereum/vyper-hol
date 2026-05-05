(*
 * Expression, iterator, and assignment-target type soundness skeleton for the
 * fresh executable Vyper type system.
 *)

Theory vyperTypeExprSoundness
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage vyperTyping
  vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeValues
  vyperTypeEnv vyperTypeBuiltins
Libs
  wordsLib

(* ===== Result predicates ===== *)

Definition no_type_error_result_def:
  no_type_error_result r <=> !msg. r <> INR (Error (TypeError msg))
End

Definition no_type_error_eval_def:
  no_type_error_eval res <=> no_type_error_result (FST res)
End

Definition expr_runtime_typed_def:
  expr_runtime_typed env e tvl <=>
    ?tv. evaluate_type env.type_defs (expr_type e) = SOME tv /\
         toplevel_value_typed tvl tv
End

Definition value_runtime_typed_def:
  value_runtime_typed env ty v <=>
    ?tv. evaluate_type env.type_defs ty = SOME tv /\ value_has_type tv v
End

Definition exprs_runtime_typed_def:
  exprs_runtime_typed env es vs <=>
    ?tvs. LIST_REL (\e tv. evaluate_type env.type_defs (expr_type e) = SOME tv) es tvs /\
          LIST_REL value_has_type tvs vs
End

Definition target_runtime_typed_def:
  target_runtime_typed env tgt gv <=> T
  (* TODO refine by relating gv locations/subscripts to type_place_target/well_typed_atarget. *)
End

(* ===== Expression soundness ===== *)

Theorem eval_expr_no_type_error:
  well_typed_expr env e /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx ==>
  no_type_error_eval (eval_expr cx e st)
Proof
  cheat
QED

Theorem eval_expr_type_preservation:
  well_typed_expr env e /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_expr cx e st = (INL tvl, st') ==>
  state_well_typed st' /\ expr_runtime_typed env e tvl
Proof
  cheat
QED

Theorem eval_expr_state_preservation_on_error:
  well_typed_expr env e /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_expr cx e st = (INR exn, st') ==>
  state_well_typed st'
Proof
  cheat
QED

Theorem eval_exprs_no_type_error:
  well_typed_exprs env es /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx ==>
  no_type_error_eval (eval_exprs cx es st)
Proof
  cheat
QED

Theorem eval_exprs_type_preservation:
  well_typed_exprs env es /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_exprs cx es st = (INL vs, st') ==>
  state_well_typed st' /\ exprs_runtime_typed env es vs
Proof
  cheat
QED

(* ===== Iterator soundness ===== *)

Theorem eval_iterator_no_type_error:
  well_typed_iterator env ty it /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx ==>
  no_type_error_eval (eval_iterator cx it st)
Proof
  cheat
QED

Theorem eval_iterator_type_preservation:
  well_typed_iterator env ty it /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_iterator cx it st = (INL vs, st') ==>
  state_well_typed st' /\
  ?tv. evaluate_type env.type_defs ty = SOME tv /\ EVERY (value_has_type tv) vs
Proof
  cheat
QED

(* ===== Target soundness ===== *)

Theorem eval_base_target_no_type_error:
  type_place_target env bt = SOME vt /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts ==>
  no_type_error_eval (eval_base_target cx bt st)
Proof
  cheat
QED

Theorem eval_target_no_type_error:
  well_typed_atarget env tgt ty /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts ==>
  no_type_error_eval (eval_target cx tgt st)
Proof
  cheat
QED

Theorem eval_targets_no_type_error:
  LIST_REL (\t ty. well_typed_atarget env t ty) tgts tys /\
  env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts ==>
  no_type_error_eval (eval_targets cx tgts st)
Proof
  cheat
QED

Theorem eval_base_target_state_preservation:
  type_place_target env bt = SOME vt /\ env_consistent env cx st /\ state_well_typed st /\
  eval_base_target cx bt st = (INL loc_sbs, st') ==>
  state_well_typed st'
Proof
  cheat
QED

